#include "api.hpp"
#include <string>
#include <iostream>
#include <set>
#include <vector>
#include <map>
using namespace std;

DFA dfa_minim(DFA &d) {
	if(d.is_empty())
		return d;
	auto alph = d.get_alphabet();
	auto states = d.get_states();
	auto initial = d.get_initial_state();
	set<string> reachable;
	reachable.insert(initial);
	bool added_dead = false;

	// Привеление ДКА к полному автомату путём добавления "мёртвого" состояния
	for(auto i = states.begin(); i != states.end(); i++)
	{
		for(auto ch = alph.begin(); ch != alph.end(); ch++)
		{
			if(!d.has_trans(*i, *ch))
			{
				if(added_dead == false)
				{
					d.create_state("DEAD");
					for(auto ch1 = alph.begin(); ch1 != alph.end(); ch1++)
					{
						d.set_trans("DEAD", *ch1, "DEAD");
					}
					added_dead = true;
				}
				d.set_trans(*i, *ch, "DEAD");
			}
		}
	}

	// Нахождение всех достежимых состояний автомата поиском в глубину
	states = d.get_states();
	bool added_state = true;
	while(added_state == true)
	{
		added_state = false;
		set<string> added;
		for(auto i = reachable.begin(); i != reachable.end(); i++)
		{
			for(auto ch = alph.begin(); ch != alph.end(); ch++)
			{
				if(d.has_trans(*i, *ch))
				{
					if(reachable.find(d.get_trans(*i, *ch)) == reachable.end())
					{
						added_state = true;
						added.insert(d.get_trans(*i, *ch));
					}
				}
			}
			if(added_state)
			{
				for(auto a = added.begin(); a != added.end(); a++)
				{
					reachable.insert(*a);
				}
			}
		}
	}

	// Удаление недостижимых состояний
	for(auto i = states.begin(); i != states.end(); i++)
	{
		if(reachable.find(*i) == reachable.end())
		{
			d.delete_state(*i);
		}
	}

	if(d.is_empty())
		return d;

	states = d.get_states();
	int n = states.size();
	vector<vector<bool> > table; // Таблица различимости состояний

	for(int i = 0; i < n; i++)
	{
		vector<bool> tmp(n, false);
		table.push_back(tmp);
	}
	map<string, int> indexes;
	map<int, string> names;
	int ind = 0;

	// Cоответствие между состояниями и их индексами в таблице
	for(auto i = states.begin(); i != states.end(); i++)
	{
		indexes[*i] = ind;
		names[ind] = *i;
		ind++;
	}

	// Заполнение таблицы

	for(auto i = states.begin(); i != states.end(); i++)
	{
		if(d.is_final(*i))
		{
			for(auto j = states.begin(); j != states.end(); j++)
			{
				if(!d.is_final(*j))
				{
					table[indexes[*i]][indexes[*j]] = true;
					table[indexes[*j]][indexes[*i]] = true;
				}
			}
		}
	}

	bool marked = true;
	while(marked)
	{
		marked = false;
		for(auto i = states.begin(); i != states.end(); i++)
		{
			auto tmp = i;
			tmp++;
			for(auto j = tmp; j != states.end(); j++)
			{
				if(table[indexes[*i]][indexes[*j]] == false)
				{
					for(auto ch = alph.begin(); ch != alph.end(); ch++)
					{
						if(d.has_trans(*i, *ch) && d.has_trans(*j, *ch))
						{
							auto st1 = d.get_trans(*i, *ch);
							auto st2 = d.get_trans(*j, *ch);
							if(table[indexes[st1]][indexes[st2]] == true)
							{
								table[indexes[*i]][indexes[*j]] = true;
								table[indexes[*j]][indexes[*i]] = true;
								marked = true;
								break;
							}
						}
					}
				}
			}
		}
	}

	// Классы эквивалентности 
	vector<set<int> > equiv;
	vector<bool> used(n, false);
	for (int i = 0; i < n; i++)
	{
		set<int> tmp;
		equiv.push_back(tmp);
	}
	for(auto i = states.begin(); i != states.end(); i++)
	{
		for(auto j = states.begin(); j != states.end(); j++)
		{
			if(table[indexes[*i]][indexes[*j]] == false)
			{
				equiv[indexes[*i]].insert(indexes[*j]);
			}
		}
	}

	// Создание нового автомата на основе полученных классов
	DFA res(alph);
	for(int i = 0; i < n; i++)
	{
		if(used[i] == false)
		{
			for(auto j = equiv[i].begin(); j != equiv[i].end(); j++)
			{
				used[*j] = true;
			}
			res.create_state(to_string(i), d.is_final(names[i]));
			if(d.is_initial(names[i]))
			{
				res.set_initial(to_string(i));
			}
		}
	}
	auto new_states = res.get_states();
	for(auto i = new_states.begin(); i != new_states.end(); i++)
	{
		int tmp_ind = stoi(*i);
		auto state = names[tmp_ind];
		for(auto ch = alph.begin(); ch != alph.end(); ch++)
		{
			if(d.has_trans(state, *ch))
			{
				auto dest = d.get_trans(state, *ch);
				int dest_ind = indexes[dest];
				string res_dest = "";
				for(auto j = new_states.begin(); j != new_states.end(); j++)
				{
					if (to_string(dest_ind) == *j)
						res_dest = *j;
				}
				if(res_dest == "")
				{
					for(int c = 0; c < n; c++)
					{
						if(equiv[c].find(dest_ind) != equiv[c].end())
						{
							for(auto it = equiv[c].begin(); it != equiv[c].end(); it++)
							{
								if(new_states.find(to_string(*it)) != new_states.end())
								{
									res_dest = to_string(*it);
								}
							}
						}
					}
				}
				res.set_trans(*i, *ch, res_dest);
			}
		}
	}

	// Повторное удаление недостежимых состояний
	new_states = res.get_states();
	set<string> new_reachable;
	set<string> dead_end;
	auto new_initial = res.get_initial_state();
	reachable.insert(new_initial);
	added_state = true;
	while(added_state == true)
	{
		added_state = false;
		for(auto i = new_reachable.begin(); i != new_reachable.end(); i++)
		{
			for(auto ch = alph.begin(); ch != alph.end(); ch++)
			{
				if(res.has_trans(*i, *ch))
				{
					bool updated = new_reachable.insert(res.get_trans(*i, *ch)).second;
					added_state = added_state || updated;
				}
			}
		}
	}
	for(auto i = new_reachable.begin(); i != new_reachable.end(); i++)
	{
		res.delete_state(*i);
	}
	
	// Удаление тупиковых состояний
	new_states = res.get_states();
	for(auto i = new_states.begin(); i != new_states.end(); i++)
	{
		set<string> from_here;
		added_state = true;
		from_here.insert(*i);
		while(added_state == true)
		{
			set<string> added;
			added_state = false;
			for(auto j = from_here.begin(); j != from_here.end(); j++)
			{
				for(auto ch = alph.begin(); ch != alph.end(); ch++)
				{
					if(res.has_trans(*j, *ch))
					{
						if(from_here.find(res.get_trans(*j, *ch)) == from_here.end())
						{
							added_state = true;
							added.insert(res.get_trans(*j, *ch));
						}
					}
				}
			}
			if(added_state)
			{
				for(auto a = added.begin(); a != added.end(); a++)
				{
					from_here.insert(*a);
				}
			}
		}
		bool has_final = false;
		for(auto j = from_here.begin(); j != from_here.end(); j++)
		{
			if(res.is_final(*j))
				has_final = true;
		}
		if(has_final == false)
		{
			dead_end.insert(*i);
		}
	}
	for(auto i = dead_end.begin(); i != dead_end.end(); i++)
	{
		res.delete_state(*i);
	}
	return res;
}
