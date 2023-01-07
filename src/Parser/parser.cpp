
#include <./include/parser.h>
int tempid=0;

std::string sym_tbl::newTemp(std::string type, std::string value)
{
    {
        tempid++;
        std::string x = "T";
        oneWord tmp(type,x + std::to_string(tempid),value,-1);
        syms.push_back(tmp);

        return x + std::to_string(tempid);
    }
}

//semantic global
//---------------------------------------//
std::stack<word> wordS;//temp store word
std::stack<sym_tbl> tableS;//symbol table
int nextquad = 0;
std::vector<Quaternion> QuadrupleForm;//TODO:或者直接push 就以全局的nextquad为下标进行存储
int offset;
std::stack<int> offsetS;

std::fstream f1;
//utility
void makelist(int quad, std::set<int>* dst);
void emit(string type, string a, string b, string addr);
int backpatch(std::set<int>list, string addr);
void merge(std::set<int>* list1, std::set<int>* list2, std::set<int>* dst);
//semantic function
std::tuple<word, std::string> Default_expression();
std::tuple<word, std::string> OR_expression();
std::tuple<word, std::string> AND_expression();
std::tuple<word, std::string> NOT_expression();
std::tuple<word, std::string> Identifier_expression();
std::tuple<word, std::string> Relop_expression();
std::tuple<word, std::string> if_();
std::tuple<word, std::string> if_else();
std::tuple<word, std::string> while_();
std::tuple<word, std::string> end_sentence();
std::tuple<word, std::string> end_sentence_2();
std::tuple<word, std::string>p78();//declaration  --> declaration_specifiers init_declarator_list ;
std::tuple<word, std::string>p2();
std::tuple<word, std::string>p62();
std::tuple<word, std::string>p88();
std::tuple<word, std::string>p93();
std::tuple<word, std::string>p94();
std::tuple<word, std::string>p95();
std::tuple<word, std::string>p96();
std::tuple<word, std::string>p97();
std::tuple<word, std::string>p98();
std::tuple<word, std::string>p99();
std::tuple<word, std::string>p100();
std::tuple<word, std::string>p101();
std::tuple<word, std::string>p102();
std::tuple<word, std::string>p103();
std::tuple<word, std::string>p36();
std::tuple<word, std::string>p32();
std::tuple<word, std::string>p33();
std::tuple<word, std::string>p34();
std::tuple<word, std::string>p37();
std::tuple<word, std::string>p11();
std::tuple<word, std::string>p12();
std::tuple<word, std::string>p4();
std::tuple<word, std::string>p47();
std::tuple<word, std::string>p48();
std::tuple<word, std::string>p42();
std::tuple<word, std::string>p43();
std::tuple<word, std::string>p44();
std::tuple<word, std::string>p45();
//---------------------------------------//


void Parser::read_grammer(const std::string path)
{
	std::fstream f;
	f.open(path,std::ios::in);
	std::fstream of;
	of.open("./result1.txt", std::ios::out);

	int generators_index=0;  // be equivalent to 31,
	if (f.is_open())
	{
		std::string tmp;
		unsigned int start_pos=0; //the start position of the substr;
		unsigned int pos;  
		while (f.eof() == false)
		{
			getline(f, tmp);
			pos=tmp.find_first_of(':', 0);
			symbol new_symbol(tmp.substr(0, pos - 0),NON_TERMINATOR,generators_index++);
			num_nontermi++;

			//cram the new non-terminator into our set
			bool r=non_terminators.insert(new_symbol).second;
			if (!r)
			{
				std::cout << "WARNING" << '\n';
				generators_index--;
			}
			symbols.insert(new_symbol);
			of << new_symbol.name << "\n";
		}
		f.close();
		of.close();
		std::cout << "g index=" << generators_index << std::endl;
	}

	f.open(path,std::ios::in);
	of.open("./result2.txt", std::ios::out);
	if (f.is_open())
	{
		//in the second pass ,we take in the terminators ,simultaneously we construct generators,
		// besides, in this part we link every non_terminator to generators whose left symbol is current non_terminator 
		//the contradiction is that we want to get the generators by symbol itself, but the generators are changing,we solve it by overloading < between symbols
		
		generator new_generator;
		std::string tmp;
		unsigned int start_pos = 0; 
		unsigned int pos;
		unsigned int order = 0;  // the order the current generator is .
		while (f.eof() == false)
		{

			getline(f, tmp);
			pos = tmp.find_first_of(':', 0);

			
			
			symbol new_nonterninator(tmp.substr(0, pos - 0), 1);
			auto ite2 = non_terminators.find(new_nonterninator);  //in virtue of the first pass, ite2 must be existed!
			new_nonterninator.generators_index = ite2->generators_index;
			new_generator.left = new_nonterninator;

			new_generator.right_list.clear();
			

			start_pos = pos + 1;
			while (pos + 1 < tmp.size())
			{
				start_pos = pos + 1;
				pos = tmp.find_first_of(' ', start_pos);
				symbol new_symbol(tmp.substr(start_pos, pos - start_pos), NON_TERMINATOR);

				if (non_terminators.find(new_symbol) == non_terminators.end())
				{
					new_symbol.type = TERMINATOR;
					num_termi++;
					terminators.insert(new_symbol);
					symbols.insert(new_symbol);
				}
				else
				{
					ite2 = non_terminators.find(new_symbol);
					new_symbol.generators_index = ite2->generators_index;
				}
				of << new_symbol.name << " ";

				new_generator.right_list.emplace_back(new_symbol);
			}
			of << '\n';

			//here we get a new generator, push it into generators_list;
			auto ite = non_terminators.find(new_nonterninator);
			if(ite != non_terminators.end())
			{
				new_generator.order = order;
				if (ite->generators_index>=generators_list.size()) //the generators_list of this non_terminators has been created
				{
					std::vector<generator> new_list;
					new_list.emplace_back(new_generator);
					generators_list.emplace_back(new_list);

				}
				else
				{
					generators_list.at(ite->generators_index).emplace_back(new_generator);
				}

				pure_generator_list.emplace_back(new_generator);// create this one for reduction procudure
			}
			++order;

		}
		f.close();
		of.close();
	}
}

void Parser::read_grammer_Yacc(const std::string path)
{
	std::fstream f(path, std::ios::in);
	if (!f.is_open())
	{
		std::cerr << "FILE WARNING::OBJECT FILE CAN NOT BE OPENED!\n";
		return;
	}
	std::fstream token_file(".//yacc_tokens.txt", std::ios::out);
	std::fstream non_file(".//yacc_non.txt", std::ios::out);
	std::fstream generators_file(".//generators.txt", std::ios::out);


	std::string tmp;
	bool read_token = true;
	unsigned int pos=0;
	unsigned int end_pos = 0;


	num_nontermi = 1; // for we need add a start

	//the same trick with the moon-parser1.0 ,we traverse the grammer for 2 passes
	// the 1st pass
	while (f.eof() == false)
	{
		getline(f,tmp);
		if (tmp.empty())
			continue;

		
		// read in all the tokens (terminator)
		if (read_token)
		{
			tmp += ' ';
			if (tmp.at(0) == '%')
				if (tmp.at(1) == '%')
					read_token = false;
				else if(tmp.at(1)!='s')
				{
					pos = tmp.find_first_of(' ');
					pos++;
					while (pos != tmp.size())
					{
						end_pos = tmp.find_first_of(' ', pos);
						symbol new_terminator(tmp.substr(pos, end_pos - pos), TERMINATOR);
						this->num_termi++;
						this->terminators.insert(new_terminator);
						this->symbols.insert(new_terminator);
						pos = end_pos + 1;
					}
				}
		}

		//read in geenrators
		else
			if (tmp.at(0) != '\t') // a new non_terminator
			{
				symbol new_nontermi(tmp, NON_TERMINATOR, num_nontermi++);
				this->non_terminators.insert(new_nontermi);
				symbols.insert(new_nontermi);
				
			}
	}
	f.close();

	symbol new_start("start", NON_TERMINATOR, 0);
	non_terminators.insert(new_start);
	this->symbols.insert(new_start);
	generator augmented_generator;
	augmented_generator.left = new_start;

	auto ite = non_terminators.find(symbol("translation_unit"));
	augmented_generator.right_list.emplace_back(*ite);
	std::vector<generator> first_list;
	first_list.emplace_back(augmented_generator);
	generators_list.emplace_back(first_list);
	pure_generator_list.emplace_back(augmented_generator);


	//2nd pass
	pos = 0;
	end_pos = 0;
	unsigned int order = 1; // the label of generator //the start order is 1 for we add a new generator before it
	f.open(path, std::ios::in);
	while (f.eof() == false)
	{
		getline(f, tmp);
		if (tmp.empty())
			continue;
		if (tmp.at(0) == '%')
			continue;

		symbol new_nontermi(tmp);

		std::set<symbol>::iterator ite;
		if ((ite=this->non_terminators.find(new_nontermi)) == non_terminators.end())
			std::cerr << "WTF\n";
		new_nontermi = *ite;

		
		//get all generators from one left symbol
		getline(f, tmp);
		tmp.erase(0, 1);
		while (tmp.at(0) != ';')
		{
			pos = end_pos = 0;
			tmp.erase(0, 2);
			generator new_generator;
			std::vector<symbol> right_list;
			new_generator.left = new_nontermi;
			
			tmp += ' ';
			while (pos != tmp.size())
			{
				end_pos = tmp.find_first_of(' ',pos);
				std::string new_symbol_name = tmp.substr(pos, end_pos - pos);
				
				if (new_symbol_name.at(0) == '\'') //analogous to '('
				{
					new_symbol_name = new_symbol_name.substr(1,new_symbol_name.size()-2);
					symbol new_symbol(new_symbol_name, TERMINATOR);
					this->terminators.insert(new_symbol);
					this->symbols.insert(new_symbol);
					right_list.emplace_back(new_symbol);
				}
				else
				{
					symbol new_symbol(new_symbol_name, NON_TERMINATOR);
					ite = this->non_terminators.find(new_symbol);
					if (ite == this->non_terminators.end())
					{
						ite = this->terminators.find(new_symbol);
						//if (ite == this->terminators.end())
							//std::cerr << "?\n";
						new_symbol.type = TERMINATOR;
					}
					else
						new_symbol.generators_index = ite->generators_index;
					right_list.emplace_back(new_symbol);
				}
				pos = end_pos + 1;
			}
			new_generator.order = order++;
			new_generator.right_list = right_list;
			if (this->generators_list.size() <= new_nontermi.generators_index)
			{
				std::vector<generator> new_generator_list;
				new_generator_list.emplace_back(new_generator);
				this->generators_list.emplace_back(new_generator_list);
			}
			else
				this->generators_list.at(new_nontermi.generators_index).emplace_back(new_generator);

			pure_generator_list.emplace_back(new_generator);
			//here we get an generator
			getline(f, tmp);
			tmp.erase(0, 1);

		}
	}

	


	std::cout << num_termi << " " << num_nontermi << "\n";
	for (auto ite = this->non_terminators.begin(); ite != non_terminators.end(); ite++)
	{
		non_file << ite->name << "\n";
	}
	for (auto ite = this->terminators.begin(); ite != terminators.end(); ite++)
	{
		token_file << ite->name << "\n";
	}

	for (const auto i : generators_list)
	{
		for (const auto j : i)
		{
			generators_file <<j.order<<"   :"<<j.left.name << " ";
			generators_file  << " --> ";
			for (const auto k : j.right_list)
				generators_file << k.name << " ";
			generators_file << "\n";
		}
		generators_file << "\n";
	}

	generators_file.close();
	token_file.close();
	non_file.close();
	f.close();

}




//	/*******to-do*****/
//	// do some semantic operation
//	/*******to-do end********/

//    int r = parser.check("token_results//4_result.txt");
//    std::cout << "the re is " << r << "\n";
	


//	return 0;
//}

void Parser::get_symbol_first(const symbol& a)
{
	//if (a.name == "operator")
		//std::cout << "g";

	if (symbol2first.find(a.name) != symbol2first.end())
		return;

	//start establishing
	std::set<symbol> first_set;

	//if a is an terminator
	if (a.type == TERMINATOR)
	{
		first_set.insert(a);
		symbol2first.insert(std::make_pair(a.name, first_set));
		return;
	}



	int index = a.generators_index;
	// i is a generator

	bool have_epsilon = true; 
	for (auto const& i : generators_list.at(index))
	{
		have_epsilon = true;
		for (auto sym : i.right_list)  
		{
			if (sym.type == TERMINATOR)
			{
				have_epsilon = false;
				first_set.insert(sym);
				break;
			}
			//non-terminator

			/** when we transfer our grammer to yacc c ,we add this we avoid the impact of left recursion*/
			if (sym.name == a.name)
			{
				have_epsilon = false;
				break;
			}
			//**end**/

			if (symbol2first.find(sym.name) == symbol2first.end())
				get_symbol_first(sym);

			auto const &tmp = symbol2first.find(sym.name);  //tmp is an iterator of map
			if (tmp->second.find(symbol("$"))==tmp->second.end()) // the episilon is not in the first set of sym
			{
				have_epsilon = false;
				std::set_union(first_set.begin(),first_set.end(), tmp->second.begin(),tmp->second.end(),std::inserter(first_set,first_set.begin()));
				break;  
			}
			else
			{
				std::set<symbol> temp = tmp->second;
				temp.erase(symbol("$", TERMINATOR, -1));  //ERASE THE EPISILON when merging the first set
				std::set_union(first_set.begin(), first_set.end(), temp.begin(), temp.end(), std::inserter(first_set, first_set.begin()));
			}

		}
		if (have_epsilon == true)
		{
			first_set.insert(symbol("$", TERMINATOR, -1));
		}
	}
	symbol2first.insert(std::make_pair(a.name, first_set));
	return;
}

void Parser::get_all_symbol_first()
{
	for (auto const& i : non_terminators)
		get_symbol_first(i);
	for (auto const& i : terminators)
		get_symbol_first(i);


	std::fstream of;
	of.open("./first_set.txt", std::ios::out);
	for (auto const& i : symbol2first)
	{
		of << "FIRST['" << i.first << "'] = { ";
		for (std::set<symbol>::iterator ite = i.second.begin(); ite != i.second.end(); ite++)
		{
			of <<"'"<<ite->name<<"'" << " ";
		}
		of << "}\n";
	}

	of.close();
}


void Parser::construct_closure(_item_group_& group)
{
	std::set<_item_> is_visited;
	std::set<_item_> is_unvisited(group.items);
	
	std::vector<std::string> re;
	std::vector<std::string> tmp;

	while (is_unvisited.empty() == false)
	{
		tmp.clear();
		re.clear();

		std::set<_item_>::iterator ite = is_unvisited.begin();
		is_visited.insert(*ite);

		if (ite->index < ite->base.right_list.size() && ite->base.right_list.at(ite->index).type == NON_TERMINATOR)
		{
			for (unsigned i = ite->index + 1; i < ite->base.right_list.size(); i++)
				tmp.emplace_back(ite->base.right_list.at(i).name);
			tmp.emplace_back(ite->prospect_symbol);
			get_sequence_first(tmp, re);

			symbol B_symbol = ite->base.right_list.at(ite->index); // in accordance with the mark in textbook
			int generators_index = non_terminators.find(B_symbol)->generators_index;

			for (const auto& i : generators_list.at(generators_index))
			{
				generator new_one(i);
				_item_ new_item(new_one, 0);

				for (const auto& pros_symbol : re)
				{
					new_item.prospect_symbol = pros_symbol;
					if (is_visited.find(new_item) == is_visited.end())
						is_unvisited.insert(new_item);
				}
			}
		}
		is_unvisited.erase(*ite);
	}
	std::set_union(group.items.begin(), group.items.end(), is_visited.begin(), is_visited.end(), std::inserter(group.items, group.items.begin()));

}

void Parser::get_sequence_first(const std::vector<std::string>& seq, std::vector<std::string>& re)
{
	for (auto const& i : seq)
	{
		std::set<symbol> tmp= this->symbol2first.find(i)->second;

		//no epsilon
		if (tmp.find(symbol("$", TERMINATOR, -1)) == tmp.end())
		{
			for (const auto& j : tmp)
				re.emplace_back(j.name);
			break;
		}
		for (const auto& j : tmp)
		{
			if(j.name!="$")
				re.emplace_back(j.name);  //no break here
		}

		//if(this->symbol2first.find(i)->second.find)
	}
}


void Parser::get_state_group_list()
{
	std::fstream of;
	of.open("_state_group_.txt", std::ios::out);

	std::set<symbol> tmp;
	tmp.insert(symbol("#", TERMINATOR, -1));
	symbol2first.insert(std::make_pair("#", tmp));

	_item_group_ first_group(0);

	symbol first_symbol("start", NON_TERMINATOR);
	int index = non_terminators.find(first_symbol)->generators_index;
	_item_ first_item(generators_list.at(index).at(0), 0);
	first_item.prospect_symbol = "#";

	first_group.items.insert(first_item);

	construct_closure(first_group);
	_item_groups_.insert(first_group);

	std::map<std::string, int> first_map;
	go_map.emplace_back(first_map);

	std::queue<_item_group_>q;
	q.push(first_group);

	unsigned int id_track = 0;

	while (q.empty() == false)
	{
		_item_group_ tmp1 = q.front();
		of << tmp1.id << "\n";
		for (auto i : tmp1.items)
		{
			of << "(" << i.base.order << " , '" << i.base.left.name << " , " << "(";
			for (auto j : i.base.right_list)
				of << "'" << j.name << "',";
			of << ") " << i.index << " (";
			of << "'" << i.prospect_symbol << "'";
			of << ')' << ')' << ",  ";

			of << "\n   ";
		}
		of << "\n";

		q.pop();



		for (auto i : symbols)
		{
			_item_group_ new_one;
			//unsigned int existed_id = -1;

			//if (i.name == "translation_unit")
			//	std::cout << "here2\n";
			state_group_go(tmp1, new_one, i.name);

			if (new_one.items.size() != 0 && _item_groups_.find(new_one) == _item_groups_.end())//a new set
			{

				new_one.id = ++id_track;

				/** here we link different item groups and restore them into the"go_map"**/
				std::map<std::string, int> new_map;
				go_map.emplace_back(new_map);
				go_map.at(tmp1.id).insert(std::make_pair(i.name, new_one.id)); // nobody will know what it means


				std::cout << "c status number: " << id_track << "\n";
				_item_groups_.insert(new_one);
				q.push(new_one);
			}
			else
			{
				if (new_one.items.size() != 0)
				{
					int dst_id = _item_groups_.find(new_one)->id;
					go_map.at(tmp1.id).insert(std::make_pair(i.name, dst_id)); // nobody will know what it means *2
				}
			}
		}
	}

	of.close();
	std::cout << "total status number: " << id_track;
}

void Parser::state_group_go(const _item_group_& scr, _item_group_& dst, std::string input)
{
	for (const auto& i : scr.items)
	{
		if (i.index < i.base.right_list.size() && input == i.base.right_list.at(i.index).name) //at least one symbol behind the point 
		{
			_item_ tmp(i.base, i.index + 1);  // the point's position move 

			//for (unsigned int cnt = i.index + 2; cnt < i.base.right_list.size(); cnt++)
			//	temp1.emplace_back(i.base.right_list.at(cnt).name);
			tmp.prospect_symbol = i.prospect_symbol;

			dst.items.insert(tmp);
		}
	}

	//here we derive items from dst's items itself
	construct_closure(dst);
}

void Parser::get_LR1_table()
{
	for (const auto& item_group_unit : _item_groups_)
	{
		movement mov;
		LR1_table.emplace_back(mov);
	}


	
	for (const auto& item_group_unit : _item_groups_)
	{
		std::set<for_verify_LR1> s;

		int index = item_group_unit.id;
		for (const auto& item_unit : item_group_unit.items)
		{
			if (item_unit.index < item_unit.base.right_list.size())
			{

				symbol a_symbol = item_unit.base.right_list.at(item_unit.index);

				if (a_symbol.type == TERMINATOR)
				{
					auto ite = go_map.at(index).find(a_symbol.name);
					if (ite != go_map.at(index).end()) //we get it
					{
						int dst = ite->second * -1;

						auto  it = s.find(for_verify_LR1(index, a_symbol.name,dst));
						if (it == s.end())
						{
							s.insert(for_verify_LR1(index, a_symbol.name, dst));

							action_struct* new_action = new action_struct(a_symbol.name, dst);
							//link this new unit to the index-th position of LR1 map

							//insert into the head!
							action_struct* tmp = LR1_table.at(index).action_ptr->next;
							new_action->next = tmp;
							LR1_table.at(index).action_ptr->next = new_action;
						}
						else
						{
							if (it->dst != dst)
							{
								std::cerr << "\nTHIS IS NOT LR1 GRAMMER!" << index << " " << a_symbol.name << "\n";
								std::cerr << it->dst << " " << dst << " " << item_unit.base.left.name << " "<<item_unit.base.order<<"\n\n";
								//it->dst = dst;
								s.erase(*it);
								s.insert(for_verify_LR1(index, a_symbol.name, dst));

								action_struct* new_action = new action_struct(a_symbol.name, dst);
								//link this new unit to the index-th position of LR1 map

								//insert into the head!
								action_struct* tmp = LR1_table.at(index).action_ptr->next;
								new_action->next = tmp;
								LR1_table.at(index).action_ptr->next = new_action;


								//move in enforcily


								//break;
							}

						}
					}
				}
			}

			if (item_unit.base.left.name == "start" && item_unit.index == 1)
			{
				//here we judge the prospect symbols
				if (item_unit.prospect_symbol=="#")
				{
					//for (const auto& i : item_unit.prospect_symbols)
					std::string i = "#";
					{
						if (i == "#")
						{

							auto  it = s.find(for_verify_LR1(index, "#", ACC));
							if (it == s.end())
							{
								s.insert(for_verify_LR1(index, "#", ACC));

								action_struct* new_action = new action_struct("#", ACC);
								//link this new unit to the index-th position of LR1 map

								//insert into the head!
								action_struct* tmp = LR1_table.at(index).action_ptr->next;
								new_action->next = tmp;
								LR1_table.at(index).action_ptr->next = new_action;
							}
							else
							{
								if (it->dst != ACC)
								{
									std::cerr << "THIS IS NOT LR1 GRAMMER!" << index << " " << "#" << "\n";
									break;
								}

							}

							/*
							action_struct* new_action = new action_struct("#", ACC);// r project
							action_struct* tmp = LR1_table.at(index).action_ptr->next;
							new_action->next = tmp;
							LR1_table.at(index).action_ptr->next = new_action;

                            const auto& it = s.find(for_verify_LR1(index, "#"));
							if (it == s.end())
								s.insert(*it);
							else
								std::cerr << "THIS IS NOT LR1 GRAMMER!\n";*/
						}
					}
					
				}
			}
			else
			{

				//r 2rd principle
				if (item_unit.index == item_unit.base.right_list.size())
				{
					if (item_unit.base.right_list.at(0).name != "$")
					{
						//for (const auto& symbol_unit : item_unit.prospect_symbols)
						auto symbol_unit = item_unit.prospect_symbol;
						{

							auto  it = s.find(for_verify_LR1(index, symbol_unit, item_unit.base.order));
							if (it == s.end())
							{
								s.insert(for_verify_LR1(index, symbol_unit, item_unit.base.order));

								action_struct* new_action = new action_struct(symbol_unit,item_unit.base.order);
								//link this new unit to the index-th position of LR1 map

								//insert into the head!
								action_struct* tmp = LR1_table.at(index).action_ptr->next;
								new_action->next = tmp;
								LR1_table.at(index).action_ptr->next = new_action;
							}
							else
							{
								if (it->dst != item_unit.base.order)
								{
									std::cerr << "THIS IS NOT LR1 GRAMMER!" << index << " " << symbol_unit << "\n";
									break;
								}

							}
							/*
							action_struct* new_action = new action_struct(symbol_unit, item_unit.base.order);// r project
							action_struct* tmp = LR1_table.at(index).action_ptr->next;
							new_action->next = tmp;
							LR1_table.at(index).action_ptr->next = new_action;

							/*const auto& it = s.find(for_verify_LR1(index, symbol_unit));
							if (it == s.end())
								s.insert(*it);
							else
								std::cerr << "THIS IS NOT LR1 GRAMMER!\n";*/
						}
						/*
						for (const auto& symbol_unit : terminators)
						{
							action_struct* new_action = new action_struct(symbol_unit.name, item_unit.base.order);// r project
							action_struct* tmp = LR1_table.at(index).action_ptr->next;
							new_action->next = tmp;
							LR1_table.at(index).action_ptr->next = new_action;
						}*/
					}
				}
				// speciallly cope with $
				if (item_unit.base.right_list.at(0).name == "$")
				{
					//for (const auto& symbol_unit : item_unit.prospect_symbols)
					auto symbol_unit = item_unit.prospect_symbol;
					{

						auto  it = s.find(for_verify_LR1(index, symbol_unit, item_unit.base.order));
						if (it == s.end())
						{
							s.insert(for_verify_LR1(index, symbol_unit, item_unit.base.order));

							action_struct* new_action = new action_struct(symbol_unit, item_unit.base.order);
							//link this new unit to the index-th position of LR1 map

							//insert into the head!
							action_struct* tmp = LR1_table.at(index).action_ptr->next;
							new_action->next = tmp;
							LR1_table.at(index).action_ptr->next = new_action;
						}
						else
						{
							if (it->dst != item_unit.base.order)
							{
								std::cerr << "THIS IS NOT LR1 GRAMMER!" << index << " " << symbol_unit << "\n";
								break;
							}

						}

						/*
						action_struct* new_action = new action_struct(symbol_unit, item_unit.base.order);// r project
						action_struct* tmp = LR1_table.at(index).action_ptr->next;
						new_action->next = tmp;
						LR1_table.at(index).action_ptr->next = new_action;

						/**const auto& it = s.find(for_verify_LR1(index, symbol_unit));
						if (it == s.end())
							s.insert(*it);
						else
							std::cerr << "THIS IS NOT LR1 GRAMMER!\n";*/
					}
				}
			}
			
			/*
			auto ite = go_map.at(index).find(item_unit.base.left.name);
			if (ite != go_map.at(index).end())
			{
				int dst = ite->second;
				goto_struct* new_goto = new goto_struct(item_unit.base.left.name,dst);// goto project
				goto_struct* tmp = LR1_table.at(index).goto_ptr->next;
				new_goto->next = tmp;
				LR1_table.at(index).goto_ptr->next = new_goto;

			}
			*/
			
		}
		for (const auto& i : non_terminators)
		{
			auto ite = go_map.at(index).find(i.name);
			if (ite != go_map.at(index).end())
			{


				int dst = ite->second;

				auto  it = s.find(for_verify_LR1(index, i.name, dst));
				if (it == s.end())
				{
					s.insert(for_verify_LR1(index, i.name, dst));

					goto_struct* new_goto = new goto_struct(i.name, dst);
					//link this new unit to the index-th position of LR1 map

					//insert into the head!
					goto_struct* tmp = LR1_table.at(index).goto_ptr->next;
					new_goto->next = tmp;
					LR1_table.at(index).goto_ptr->next = new_goto;
				}
				else
				{
					if (it->dst != dst)
					{
						std::cerr << "THIS IS NOT LR1 GRAMMER!" << index << " " << i.name<< "\n";
						break;
					}

				}

				/*
				goto_struct* new_goto = new goto_struct(i.name, dst);// goto project
				goto_struct* tmp = LR1_table.at(index).goto_ptr->next;
				new_goto->next = tmp;
				LR1_table.at(index).goto_ptr->next = new_goto;
				*/

			}
		}
	}
	make_cache();
}

void Parser ::print_LR1_table()
{
	std::fstream of;
	of.open("./LR1_table_c.txt", std::ios::out);
	for (unsigned int i = 0; i < LR1_table.size(); i++)
	{
		// traverse 2 link lists
		of << std::setw(5) << i << "\n";
		of << "ACTION\n";
		action_struct* track = LR1_table.at(i).action_ptr->next;
		while (track != nullptr)
		{
			of << track->symbol_name << " ";
			if (track->dst < 0)//s
				of << "s" << -1 * track->dst;
			else
				of << "r" << 1 * track->dst;
			of << "  ||   ";
			track = track->next;
		}

		of << "\nGOTO\n";

		goto_struct* track2 = LR1_table.at(i).goto_ptr->next;
		while (track2 != nullptr)
		{
			of << track2->symbol_name << " ";
			//if (track->dst < 0)//s
				//of << "s" << -1 * track->dst;
			//else
				of << 1 * track2->dst;
			of << "  ||   ";
			track2 = track2->next;
		}
		of << "\n\n";
	}
}

void Parser::make_cache()
{
	std::fstream of("cache", std::ios::out);
	of << LR1_table.size() << "\n";
	for (unsigned int i = 0; i < LR1_table.size(); i++)
	{
		of << "action\n";
		action_struct* track= LR1_table.at(i).action_ptr->next;
		while (track != nullptr)
		{
			of << track->symbol_name << " "<<track->dst<<"\n";
			track = track->next;
		}

		of << "goto\n";

		goto_struct* track2 = LR1_table.at(i).goto_ptr->next;
		while (track2 != nullptr)
		{
			of << track2->symbol_name << " "<< 1 * track2->dst<<"\n";
			track2 = track2->next;
		}
		of << "\n";
	}
	of.close();
}

int Parser::read_cache()
{
	std::fstream f("cache", std::ios::in);
	std::string tmp;
    unsigned int size;

	std::string name;
	int dst;
    int tag=false;
	if (f.is_open())
	{
        tag=true;
		getline(f,tmp);
		std::stringstream sstrem(tmp);
		sstrem >> size;
		std::cout << "size'" << size << "\n";
		for (unsigned int i = 0; i < size; i++)
		{
			movement mov;
			action_struct* track1 = mov.action_ptr;
			goto_struct* track2 = mov.goto_ptr;

			getline(f, tmp); //readin the "action"
			getline(f, tmp);
			while(tmp!="goto")
			{
				std::stringstream strs(tmp);
				
				strs >> name;
				strs>> dst;
				action_struct* new_action = new action_struct(name,dst);
				track1->next = new_action;
				track1 = new_action;
				getline(f, tmp);
		
			}

			getline(f, tmp);
			while (tmp.empty() == false)
			{
				std::stringstream strs(tmp);

				strs >> name;
				strs >> dst;
				goto_struct* new_goto = new goto_struct(name, dst);
				track2->next = new_goto;
				track2 = new_goto;
				getline(f, tmp);
			}

			LR1_table.emplace_back(mov);
		}
    }
    f.close();

    return tag;
}

//we use the following command to generate the pic
//neato -Tpng D://compilationprinciple/parser/parser/DFA.dot -o D://compilationprinciple//parser//parser//DFA.png
void Parser::print_DFA()
{
    std::fstream of;
    of.open("./DFA.dot", std::ios::out);

    of << "digraph G{\n";

    of << "graph[dpi=500, autosize=false,size=\"150,150\"];\n";

    of << "overlap=false;\nspines=true;\n";

    of << "node [shape=box];\n";
    of<<"edge[lblstyle = \"above, sloped\"];\n";

    for (const auto& unit : _item_groups_)
    {
        of << "node" << unit.id << "[label=\" ";

        //write the items into a node
        /*
        for (auto item_unit : unit.items)
        {
            of << item_unit.base.left.name << " -> ";
            for (unsigned int i = 0; i < item_unit.base.right_list.size(); i++)
            {
                if (i == item_unit.index)
                    of << ".";
                if (item_unit.base.right_list.at(i).name != "$")
                    of << item_unit.base.right_list.at(i).name;
            }
            of << "  ";

            //prospect symbol
            for (auto prospect_unit : item_unit.prospect_symbols)
                of << prospect_unit << " | ";
            of << "\\n";
        }
        */
        of << unit.id;
        of << "\"]";
        of << "\n";
    }

    //here we start to output the relationships between item_groups
    of << "\n";

    int cnt = 0;
    for (const auto item_group_map : go_map)
    {
        for (const auto& go_relation : item_group_map)
        {
            std::string label = go_relation.first;
            of << "node" << cnt << "->" << "node" << go_relation.second << "\n ";// [label = \"" << label << "\",constraint=false]\n";
        }
    }
    of << "}";
    of.close();
}

//semantic action
//--------------------------------//
//utility
//-----------
void makelist(int quad, std::set<int>* dst)
{
    dst->clear();
    dst->insert(quad);
}
void emit(string type, string a, string b, string addr)
{
    // int i=nextquad;
    // QuadrupleForm[i]=Quaternion(type,a,b,addr);
    QuadrupleForm.push_back(Quaternion(type, a, b, addr));
    nextquad++;
    // f1 << "( " << type << ", " << a << " " << b << " " << addr << " )"<<std::endl ;
}
bool _IsDigit(const string a)
{
    for (auto it : a)
        if (!isdigit(it))
            return false;
    return true;
}
int backpatch(std::set<int>list, string addr)
{
    for (int i : list) {
        if (QuadrupleForm[i].addr != "INIT_STATE")
            {
            string temp = QuadrupleForm[i].addr;
                 if (_IsDigit(temp))
                   return ERROR;
                    }//already exist
        else
            QuadrupleForm[i].addr = addr;
    }
    return SUCCESS_;
}
void merge(std::set<int>* list1, std::set<int>* list2, std::set<int>* dst)
{
    std::set_union(list1->begin(), list1->end(), list2->begin(), list2->end(), std::inserter(*dst, dst->begin()));
}

//default function to get son's attribute
std::tuple<word, std::string> Default_expression()
{
    word id = wordS.top();
    wordS.pop();
    word temp(LINEOFNONT,LINEOFNONT, id.value,id.realV,0);
    word* E = &temp;
    E->nextlist = id.nextlist;
    E->falselist = id.falselist;
    E->truelist = id.truelist;
    E->quad = id.quad;

    return std::make_tuple(*E, "None");
}
//bool expression
//-----------
//bool operator
//58: logical_or_expression-->logical_or_expression OR_OP logical_and_expression
std::tuple<word, std::string> OR_expression()//E->E1 or E2
{
    word E1 = wordS.top();
    wordS.pop();
    wordS.pop();//OR
    word E2 = wordS.top();
    wordS.pop();
    word temp(LINEOFNONT,LINEOFNONT, 0);
    word* E = &temp;

    E->quad = std::to_string(nextquad);//replace the function of M

    if (backpatch(E1.falselist, E2.quad) == ERROR)
            return std::make_tuple(*E, "SEMANTIC ERROR::backpatch error in OR_expression in " + E1.realV + " falselist\n");
        // return std::make_tuple(*E, "SEMANTIC ERROR::backpatch error in " + E1.value + " falselist\n");

        merge(&(E1.truelist), &(E2.truelist), &(E->truelist));
        E->falselist = E2.falselist;

        return std::make_tuple(*E, "None");
}
//56: logical_and_expression-->logical_and_expression AND_OP inclusive_or_expression
std::tuple<word, std::string> AND_expression()//E->E1 and E2
{
    word E1 = wordS.top();
    wordS.pop();
    wordS.pop();//AND
    word E2 = wordS.top();
    wordS.pop();
    word temp(LINEOFNONT,LINEOFNONT, 0);
    word* E = &temp;

    E->quad = std::to_string(nextquad);//replace the function of M

    if (backpatch(E1.truelist, E2.quad) == ERROR)
            return std::make_tuple(*E, "SEMANTIC ERROR::backpatch error in AND_expression in " + E1.realV + " truelist\n");
        // return std::make_tuple(*E, "SEMANTIC ERROR::backpatch error in " + E1.value + " truelist\n");
        E->truelist = E2.truelist;
        merge(&(E1.falselist), &(E2.falselist), &(E->falselist));

        return std::make_tuple(*E, "None");
}
//20: unary_expression--> unary_operator cast_expression
std::tuple<word, std::string> NOT_expression()//E->not E1
{
    wordS.pop();//NOT
    word E1 = wordS.top();
    wordS.pop();

    word temp(LINEOFNONT,LINEOFNONT, 0);
    word* E = &temp;

    E->quad = std::to_string(nextquad);//replace the function of M

    E->truelist = E1.falselist;
    E->falselist = E1.truelist;

    return std::make_tuple(*E, "None");
}
//1: primary_expression--> IDENTIFIER——may not，or will cause confliction
//4: primary_expression  --> ( expression ) ——may yes
std::tuple<word, std::string> Identifier_expression()//E->id
{
    wordS.pop();// (
    word id = wordS.top();
    wordS.pop();// expression
    wordS.pop();// )

    word temp(LINEOFNONT,LINEOFNONT,0);
    word* E = &temp;

    E->quad = std::to_string(nextquad);//replace the function of M

    makelist(nextquad, &E->truelist);
    makelist(nextquad + 1, &E->falselist);
    emit("jnz", id.value, "None", "INIT_STATE");
    emit("j", "None", "None", "INIT_STATE");

    return std::make_tuple(*E, "None");
}
//根据语法文件：bool里的（）被包含在控制语句里了
// int BRANKET_expression(symbol*E,symbol*E1)
// {
//     E->quad=nextquad;//replace the function of M
//     E->truelist=E1->truelist;
//     E->falselist=E1->falselist;

//     return SUCCESS_;
// }
// 42: relational_expression  --> relational_expression < shift_expression
// 43: relational_expression  --> relational_expression > shift_expression
// 44: relational_expression  --> relational_expression LE_OP shift_expression
// 45: relational_expression  --> relational_expression GE_OP shift_expression
// 47: equality_expression  --> equality_expression EQ_OP relational_expression
// 48: equality_expression  --> equality_expression NE_OP relational_expression
std::tuple<word, std::string> Relop_expression()//E->id1 relop id2
{
    word id1 =  wordS.top();
    wordS.pop();
    word relop =  wordS.top();
    wordS.pop();
    word id2 =  wordS.top();
    wordS.pop();

    word temp(LINEOFNONT,LINEOFNONT,0);
    word* E = &temp;
    //revise
    string relop_op = relop.realV;
    if (relop.realV == "LE_OP")
        relop_op = "<=";
    else if (relop.realV == "GE_OP")
        relop_op = ">=";
    else if (relop.realV == "EQ_OP")
        relop_op = "=";
    else if (relop.realV == "NE_OP")
        relop_op = "!=";

    E->quad = std::to_string(nextquad);//replace the function of M

    makelist(nextquad, &E->truelist);
    makelist(nextquad + 1, &E->falselist);

    string type = "j" + relop_op;
    emit(type, id1.value, id2.value, "INIT_STATE");
    emit("j", "None", "None", "INIT_STATE");

    return std::make_tuple(*E, "None");
}
//control sentences
//-----------
//207: selection_statement--> IF ( expression ) statement
std::tuple<word, std::string> if_()//S->if E S1
{
    wordS.pop();//IF
    wordS.pop();//(
    word  E =  wordS.top();
    wordS.pop();//expression
    wordS.pop();//)
    word  S1 =  wordS.top();
    wordS.pop(); //statement

    word temp(LINEOFNONT, LINEOFNONT, 0);
    word* S = &temp;

    S->quad = std::to_string(nextquad);//replace the function of M

    if (backpatch(E.truelist, S1.quad) == ERROR)//S1->quad has been stored in relop/bool operation
            return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in if in " + E.realV + " truelist\n");
        // return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in " + E.value + " truelist\n");
        merge(&E.falselist, &S1.nextlist, &S->nextlist);

        return std::make_tuple(*S, "None");
}
//208: selection_statement--> IF ( expression ) statement ELSE statement
std::tuple<word, std::string> if_else()//S->if E S1 else S2
{
    wordS.pop();//IF
    wordS.pop();//(
    word E =  wordS.top();
    wordS.pop();//expression
    wordS.pop();//)
    word S1 =  wordS.top();
    wordS.pop(); //statement
    word N =  wordS.top();
    wordS.pop(); // ELSE(replace N)
    word S2 =  wordS.top();
    wordS.pop(); //statement

    word temp(LINEOFNONT,LINEOFNONT,  0);
    word* S = &temp;

    S->quad = std::to_string(nextquad);//replace the function of M

    if (backpatch(E.truelist, S1.quad) == ERROR)
            return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in if_else in " + E.realV + " truelist\n");
        // return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in " + E.value + " truelist\n");
        if (backpatch(E.falselist, S2.quad) == ERROR)
            return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in if_else in " + E.realV + " falselist\n");
        // return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in " + E.value + " falselist\n");
        merge(&S1.nextlist, &S2.nextlist, &S->nextlist);
        merge(&S->nextlist, &N.nextlist, &S->nextlist);

        return std::make_tuple(*S, "None");
}
//210: iteration_statement--> WHILE ( expression ) statement
std::tuple<word, std::string> while_()//S->while E do S1
{
    wordS.pop();//WHILE
    wordS.pop();//(
    word E =  wordS.top();
    wordS.pop();//expression
    wordS.pop();//)
    word S1 =  wordS.top();
    wordS.pop(); //statement

    word temp(LINEOFNONT,LINEOFNONT,  0);
    word* S = &temp;

    S->quad = std::to_string(nextquad);//replace the function of M

    if (backpatch(S1.nextlist, E.quad) == ERROR)
            return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in while in " + S1.realV + " nextlist\n");
        if (backpatch(E.truelist, S1.quad) == ERROR)
            return std::make_tuple(*S, "SEMANTIC ERROR::backpatch error in while in " + E.realV + " truelist\n");
        S->nextlist = E.falselist;
        emit("j", "None", "None", E.quad);

        return std::make_tuple(*S, "None");
}
std::tuple<word, std::string> end_sentence()//L->L1;
{
    word L1 =  wordS.top();
    wordS.pop();//expression
    wordS.pop();// ;

    word temp(LINEOFNONT,LINEOFNONT,  0);
    word* L = &temp;


    if (!L1.nextlist.empty()) {//really bool/control sentences
            if (backpatch(L1.nextlist, std::to_string(nextquad)) == ERROR)
                return std::make_tuple(*L, "SEMANTIC ERROR::backpatch error in end_sentence in " + L1.realV + " nextlist\n");
            // return std::make_tuple(*L, "SEMANTIC ERROR::backpatch error in " + L1.value + " nextlist\n");
            L->nextlist = L1.nextlist;
        }
        return std::make_tuple(*L, "None");
}
//205 : expression_statement -> ;
std::tuple<word, std::string> end_sentence_2()//L-> ;
{
    word delimiter = wordS.top();
    wordS.pop();// ;

    word temp(LINEOFNONT,LINEOFNONT,  0);
    word* L = &temp;
    L->quad = std::to_string(nextquad);
    makelist(nextquad, &L->nextlist);

    return std::make_tuple(*L, "None");
}
//--------------------------------//

void Parser::init()
{
    sym_tbl all_t("global");
    tableS.push(all_t);
    nextquad = 0;
    for (int i = 0; i < 229; i++)
        p[i] = Default_expression;

    //assign & declarations
    p[78] = p78;
        p[2] = p2;
        p[62] = p62;
        p[88] = p88;
        p[93] = p93;
        p[94] = p94;
        p[95] = p95;
        p[96] = p96;
        p[97] = p97;
        p[98] = p98;
        p[99] = p99;
        p[100] = p100;
        p[101] = p101;
        p[102] = p102;
        p[103] = p103;
        p[36] = p36;
        p[32] = p32;
        p[33] = p33;
        p[34] = p34;
        p[37] = p37;
        p[11] = p11;
        p[12] = p12;
        p[4] = p4;
        p[42] = p42;
        p[43] = p43;
        p[44] = p44;
        p[45] = p45;
        p[47] = p47;
        p[48] = p48;

        //control & bool
        p[58] = OR_expression;
        p[56] = AND_expression;
        p[20] = NOT_expression;
        p[4] = Identifier_expression;
        p[42] = Relop_expression;
        p[43] = Relop_expression;
        p[44] = Relop_expression;
        p[45] = Relop_expression;
        p[47] = Relop_expression;
        p[48] = Relop_expression;
        p[207] = if_;
        p[208] = if_else;
        p[210] = while_;
        p[206] = end_sentence;
        p[205] = end_sentence_2;
}
//primary_expression  --> CONSTANT
std::tuple<word, std::string>p2()
{
    word const_exp = wordS.top();
    wordS.pop();

    word pushWord(LINEOFNONT,LINEOFNONT, "primary_expression", const_exp.realV, 0);
    pushWord.type = "CONSTANT";
    return std::make_tuple(pushWord, "None");
}

std::tuple<word, std::string>p11()//postfix_expression  --> postfix_expression INC_OP
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();

    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;

    sym_tbl cur_t = tableS.top();
    oneWord left = cur_t.lookup(a);

    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) + 1));

    emit("+", a, "1", temp);
    emit(":=", temp, "None", a);
    word pushWord(LINEOFNONT, LINEOFNONT, "postfix_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p12()//postfix_expression  --> postfix_expression INC_OP
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();

    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;

    sym_tbl cur_t = tableS.top();
    oneWord left = cur_t.lookup(a);

    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) - 1));

    emit("-", a, "1", temp);
    emit(":=", temp, "None", a);
    word pushWord(LINEOFNONT, LINEOFNONT, "postfix_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
//additive_expression-- > additive_expression + multiplicative_expression
std::tuple<word, std::string>p36()
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) + atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("+", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "additive_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p32()
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) * atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("*", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "additive_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p33()
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) / atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("/", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "additive_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p34()
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) % atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("%", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "additive_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p37()
{
    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) - atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("-", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "additive_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p78()//declaration  --> declaration_specifiers init_declarator_list ;
{
    word decSpec = wordS.top();
    wordS.pop();
    word initDec = wordS.top();
    wordS.pop();
    // pop "declaration_specifiers init_declarator_list"
    std::string type = decSpec.realV;
    std::string name = initDec.realV;
    std::string value = initDec.rrealv;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord t(type, name, value, offset);
    cur_t.addsys(t);
    tableS.push(cur_t);
    offset += initDec.width;
    offsetS.push(offset);
    word pushWord(LINEOFNONT, LINEOFNONT, "declaration", "declaration", 0);
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p93()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "VOID", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p94()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "CHAR", 0);
    pushWord.width = 1;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p95()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "SHORT", 0);
    pushWord.width = 2;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p96()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "INT", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p97()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "LONG", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p98()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "FLOAT", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p99()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "DOUBLE", 0);
    pushWord.width = 8;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p100()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "SIGNED", 0);
    pushWord.width = 2;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p101()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "UNSIGNED", 0);
    pushWord.width = 2;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p102()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "struct_or_union_specifier", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p103()
{
    wordS.pop();

    word pushWord(LINEOFNONT, LINEOFNONT, "type_specifier", "enum_specifier", 0);
    pushWord.width = 4;
    return std::make_tuple(pushWord, "None");
}
std::tuple<word, std::string>p62()
{
    word unary_exp = wordS.top();
    wordS.pop();
    word ass_opt = wordS.top();
    wordS.pop();
    word ass_exp = wordS.top();
    wordS.pop();

    std::string wrongInfo = "None";

    std::string a = ass_exp.realV;

    sym_tbl cur_t = tableS.top();
    oneWord left = cur_t.lookup(a);

    if (left.name == "None" && ass_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        //std::cout << a << std::endl;
        return std::make_tuple(re, wrongInfo);
    }


    emit(ass_opt.realV, ass_exp.realV, "-", unary_exp.realV);
    word pushWord(LINEOFNONT, LINEOFNONT, "assignment_expression", ass_exp.rrealv, 0);

    return std::make_tuple(pushWord, "None");
}
//init_declarator  --> declarator = initializer

std::tuple<word, std::string>p88()
{
    word unary_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word ass_exp = wordS.top();
    wordS.pop();
    //std::cout << ass_exp.realV << " 1" << std::endl;

    std::string wrongInfo = "None";

    std::string a = ass_exp.realV;

    sym_tbl cur_t = tableS.top();
    oneWord left = cur_t.lookup(a);

    if (left.name == "None" && ass_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }

    emit("=", ass_exp.realV, "-", unary_exp.realV);
    word pushWord(LINEOFNONT, LINEOFNONT, "init_declarator", unary_exp.realV, 0);

    return std::make_tuple(pushWord, "None");
}
//primary_expression  --> ( expression )
std::tuple<word, std::string>p4()
{

    wordS.pop();
    word unary_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    return std::make_tuple(unary_exp, "None");
}
std::tuple<word, std::string>p47()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str())== atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("==", a, b, temp);
    std::cout << temp;
    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p48()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) != atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("!=", a, b, temp);
    std::cout << temp;
    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}

std::tuple<word, std::string>p42()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) < atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("<", a, b, temp);

    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}

std::tuple<word, std::string>p43()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) > atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit(">", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p44()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) <= atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit("<=", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}
std::tuple<word, std::string>p45()
{

    word mul_exp = wordS.top();
    wordS.pop();
    wordS.pop();
    word cast_exp = wordS.top();
    wordS.pop();
    std::string wrongInfo = "None";

    std::string a = mul_exp.realV;
    std::string b = cast_exp.realV;
    sym_tbl cur_t = tableS.top();
    tableS.pop();
    oneWord left = cur_t.lookup(a);
    oneWord right = cur_t.lookup(b);
    if (left.name == "None" && mul_exp.type != "CONSTANT" || right.name == "None" && cast_exp.type != "CONSTANT") {
        wrongInfo = "SEMANTIC ERROR::use undeclared variable\n";
        word re(LINEOFNONT, LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }
    /*if (left.type != right.type) {
        wrongInfo = "wrong type";
        word re(LINEOFNONT, "error", "error", -1);
        return std::make_tuple(re, wrongInfo);
    }*/
    std::string temp = cur_t.newTemp(left.type, std::to_string(atoi(left.value.c_str()) >= atoi(right.value.c_str())));
    tableS.push(cur_t);
    emit(">=", a, b, temp);
    word pushWord(LINEOFNONT, LINEOFNONT, "relational_expression", temp, 0);
    return std::make_tuple(pushWord, wrongInfo);
}

//TODO: MEND this function
std::tuple<bool, std::string, int, int> Parser::check(const std::string path)
{
    //track the max number of stack
      // 1
    unsigned int max_num = 0;

    int nodeID = 0;
    int eplisonID = 2147483647;
    std::fstream f;
    f.open(path, std::ios::in);
    std::fstream of;
    of.open("./grammer_tree.dot", std::ios::out);
    std::fstream tmp_file;
    tmp_file.open("stack.tmp", std::ios::out);

    while (!itemS.empty())
        itemS.pop();
    while (!symbolS.empty())
        symbolS.pop();
    /////////////////////////////////
    itemS.push(0);// I0 into stack
    symbolS.push(word(-1, -1, "#", "#", -1));
    //6
    tmp_file << "p" << " " << 0 << " " << "#\n";

    of << "digraph G{\ngraph[dpi=300,autosize=false,size=\"200, 200\"];\noverlap=false; \nspines=true;\nnode[ shape=\"box\"];\n";

    while (f.eof() == false)
    {
        bool findFLAG = false, R_flag = false;
        unsigned int pos = 0, pos1 = 0, pos2 = 0;
        std::string tmp;

        getline(f, tmp);
        pos = tmp.find_first_of(' ');
        pos1 = tmp.find_first_of(' ', pos + 1);
        pos2 = tmp.find_first_of(' ', pos1 + 1);

        word inputw(atoi(tmp.substr(0, pos - 0).c_str()), atoi(tmp.substr(pos + 1, pos1 - pos - 1).c_str()), tmp.substr(pos1 + 1, pos2 - pos1 - 1), tmp.substr(pos2 + 1, tmp.size() - pos2 - 1), nodeID);

        tmp_file << "@ " << inputw.value << "\n";
        int topState = itemS.top();

        action_struct* a_ptr = LR1_table[topState].action_ptr->next;

        bool syntax_tag = false;////
        bool semantic_tag = true;////
        int error_line = 0, error_col = 0;////
        std::string error_message;
        while (a_ptr)
        {
            R_flag = false;
            if (a_ptr->symbol_name == inputw.value)
            {
                syntax_tag = true;
                if (a_ptr->dst == ACC)
                {
                    of << "}\n";

                    //4
                    tmp_file << "b\n";
                    tmp_file << "#\n";

                    //output to ressem.txt
                    f1.open("IR.txt",std::ios::out);
                    for (int i = 0; i < QuadrupleForm.size(); i++)
                    {
                        auto it = QuadrupleForm[i];
                        f1 << i << ' ' << "( " << it.type << ", " << it.a << ", " << it.b << ", " << it.addr << " )" << std::endl;
                    }
                    f1.close();
                    if(of.is_open())
                        of.close();
                    return std::make_tuple(true, "none", 0, 0);
                }
                findFLAG = true;
                if (a_ptr->dst < 0)
                {//s
                    itemS.push(-a_ptr->dst);
                    nodeID++;
                    inputw.setID(nodeID);

                    if (inputw.value == "ELSE")
                    {//"else"——special_judge to replace N
                        makelist(nextquad, &(inputw.nextlist));
                        emit("j", "None", "None", "INIT_STATE");
                    }
                    symbolS.push(inputw);
                    //7
                    tmp_file << "p " << -a_ptr->dst << " " << inputw.value << "\n";
                    //2
                    if (itemS.size() > max_num)
                        max_num = itemS.size();
                    break;
                }
                else if (a_ptr->dst > 0)
                {//r
                    syntax_tag = false;
                    generator x = pure_generator_list[a_ptr->dst];
                    nodeID++;
                    int fid = nodeID;

                    //word fword(LINEOFNONT, x.left.name, x.left.name, fid);
                    word fword;
                    std::string type;
                    bool isTrans = false;
                    of << "node" << nodeID << "[label=\"" << x.left.name << "\"]\n";
                    /*-----------------------------*/
                    if (x.right_list.at(0).name != "$")
                    {
                        int n = x.right_list.size();
                        for (int i = 0; i < n; i++)
                        {
                            word topW = symbolS.top();
                            if (n == 1)
                            {
                                fword = topW;
                                type = topW.type;
                                isTrans = true;
                            }
                            //
                            if (p[a_ptr->dst] != Default_expression)
                            {
                                wordS.push(topW);
                            }
                            //wordS.push(topW);

                            if (topW.line != LINEOFNONT)
                                of << "node" << topW.id << "[label=\"" << topW.value << "\\n" << topW.realV << "\"]\n";
                            of << "node" << fid << "->node" << topW.id << "\n";

                            symbolS.pop();
                            itemS.pop();

                            //8
                            tmp_file << "b\n";
                        }
                    }
                    else
                    {
                        eplisonID--;
                        of << "node" << eplisonID << "[label=\"Eplison\"]\n";
                        of << "node" << fid << "->node" << eplisonID << "\n";
                    }/**/
                    topState = itemS.top();

                    //semantic func
                    if (p[a_ptr->dst] != Default_expression) {
                        auto fx = p[a_ptr->dst]();
                        fword = std::get<0>(fx);

                        //test
                        string message = std::get<1>(fx);
                        if (message != "None")
                        {
                            error_message = message;
                            semantic_tag = false;
                            error_col = inputw.col;
                            error_line = inputw.line;
                            std::cout << "123333" << ' ' << error_line << ' ' << error_col << ' ' << message << "\n";
                            break;
                        }
                        std::cout << error_line << ' ' << error_col << ' ' << message << "\n";

                        //auto [fword,wronginfo] = p[a_ptr->dst]();
                    }
                    else
                    {
                        fword.value = x.left.name;
                        fword.type = type;
                        if (fword.quad == "")//to prevent S/E has no attributes(quad,nextlist...) like if(a){ int b;int c;} (S1 has no attribute)
                            fword.quad = std::to_string(nextquad - 1);
                        if (fword.nextlist.empty())
                            makelist(nextquad - 1, &fword.nextlist);
                        //std::cout << fword.value<<" "<< fword.type<<std::endl;
                        if (!isTrans)
                            fword = word(LINEOFNONT, LINEOFNONT, x.left.name, x.left.name, fid);
                        else
                        {
                            //fword.value = x.left.name;
                            fword.id = fid;
                        }
                    }
                    fword.setFid(fid);
                    fword.value = x.left.name;
                    symbolS.push(fword);

                    //goto
                    goto_struct* g_ptr = LR1_table[topState].goto_ptr->next;
                    while (g_ptr)
                    {
                        if (g_ptr->symbol_name == x.left.name)
                        {
                            syntax_tag = true;
                            R_flag = true;
                            itemS.push(g_ptr->dst);

                            //9
                            tmp_file << "p " << g_ptr->dst << " " << fword.value << "\n";
                            //3

                            break;
                        }
                        g_ptr = g_ptr->next;
                    }
                    if (R_flag == true)
                    {
                        topState = itemS.top();
                        a_ptr = LR1_table[topState].action_ptr->next;
                        continue;
                    }
                    break;
                }
            }
            a_ptr = a_ptr->next;
        }
        if (a_ptr == nullptr)
        {
            syntax_tag = false;
            tmp_file.close();
            if(of.is_open())
                of.close();
            return std::make_tuple(false, "SYNTAX ERROR::syntax error\n", inputw.line, inputw.col);
        }
        if (semantic_tag == false)
        {
            tmp_file.close();
            if(of.is_open())
                of.close();
            return std::make_tuple(false, error_message, error_line, error_col);
        }
        if (syntax_tag == false)
        {
            tmp_file.close();
            if(of.is_open())
                of.close();
            return std::make_tuple(false, "SYNTAX ERROR::syntax error\n", inputw.line, inputw.col);
        }
        if (findFLAG == false && R_flag == false) {
            //of << "}\n";

            ///5
            tmp_file.close();
            if(of.is_open())
                of.close();
            return std::make_tuple(false, "SYNTAX ERROR::syntax error\n", inputw.line, inputw.col);
        }
    }
}
//


