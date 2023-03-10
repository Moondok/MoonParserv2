

#include <vector>
#include <fstream>
#include <string>
#include <set>
#include <vector>
#include <iostream>
#include <map>
#include <algorithm>
#include <queue>
#include <iomanip>
#include <stack>
#include <sstream>

const bool NON_TERMINATOR=1;
const bool TERMINATOR = 0;
const int ACC = -10086;

#define SYNTAX_SUCCESS -1 //

#define LINEOFNONT -2  //
//semantic definitions
#define SUCCESS_ 0
#define ERROR -1
using string = std::string;


struct action_struct
{
	std::string symbol_name;
	int dst;
	action_struct():symbol_name("head"),dst(-1) {}
	action_struct(const std::string& s, const int d) :symbol_name(s), dst(d) {}
	action_struct* next = nullptr;
};

struct goto_struct
{
	std::string symbol_name;
	int dst;
	goto_struct* next = nullptr;
	goto_struct():symbol_name("head"), dst(-1) {}
	goto_struct(const std::string& s, const int d) :symbol_name(s), dst(d) {}
};

struct movement
{
	action_struct* action_ptr;
	goto_struct* goto_ptr;

	movement()
	{
		action_ptr = new action_struct("head", -1);
		goto_ptr = new goto_struct("head", -1);
	}
};

struct for_verify_LR1
{
	int index;
	std::string name;
	int dst;

	bool operator < (const for_verify_LR1&a) const
	{
		if (index != a.index)
			return index < a.index;
		else
			return name < a.name;
	}

	for_verify_LR1(int i, std::string n,int d):index(i),name(n),dst(d)
	{

	}
};

class symbol  //
{
public:
	
	std::string name;
	bool type=0;  //0 presents terminator ,vice versa
	int generators_index = -1;
	symbol()
	{

	}
	symbol(std::string n, bool t=0,int i=-1) :name(n), type(t),generators_index(i)
	{};

	bool operator <(const symbol& a) const
	{
		return this->name<a.name;
	}

	/*bool operator ==(const symbol& a) const
	{
		return this->name == a.name;
	}*/

	/********TO-DO*******/
	// add some attributes for semantic analysis

	/*********to-do-end***************/


	/********TO-DO*******(optional)
	// add some function for semantic analysis

    ********to-do-end***************/


};


class generator
{
public:
	symbol left;
	std::vector<symbol> right_list;
	unsigned int order=0;

	bool operator<(const generator& a) const
	{
		return this->order < a.order; //same order, same content
	}

	generator(symbol l, std::vector<symbol> r_list, unsigned int o) :left(l), right_list(r_list), order(o)
	{}
	generator(const generator& a) :left(a.left), right_list(a.right_list), order(a.order)
	{}
	generator()
	{ }
};

class _item_
{
public :
	const generator base;
	unsigned int index;
	std::string prospect_symbol;

	bool operator< (const _item_& a) const
	{
		if (this->base < a.base || a.base < this->base)
		{
			return this->base < a.base;
		}
		else if (this->index<a.index || this->index>a.index)
			return this->index < a.index;
		else
			return this->prospect_symbol < a.prospect_symbol;
	}

	_item_(const generator& g, const unsigned int i) :base(g), index(i) {}

};

class _item_group_
{
public:
	unsigned int id;
	std::set<_item_> items;
	bool operator<(const _item_group_& a) const
	{
		if (this->items.size() != a.items.size())
			return this->items.size() < a.items.size();
		std::set<_item_>::iterator ite = this->items.begin();
		bool tag = false;
		for (auto const& i : a.items)
		{
			if (*ite < i || i < *ite)
				return *ite < i;
			ite++;
		}
		return tag;
	}

	_item_group_(const unsigned int i) :id(i) {}

	_item_group_() {}

	
};

class word
{
public:
	int line;
	int id;
    int width;
	std::string value;
	std::string realV;
    std::string type;
    std::string rrealv;//for a=1..
    //control&bool properties
    std::set<int> truelist;
    std::set<int> falselist;
    std::set<int> nextlist;
    std::string quad;

    word(){};

	word(int line, std::string value, std::string realV, int id) {
		this->line = line;
		this->value = value;
		this->realV = realV;
		this->id = id;
	}
    word(int line,int id)
    {
            this->line = line;
           this->id = id;
    }
    void setID(int id)
    {
		this->id = id;
	}
    word(const word& c)
    {
        this->width = c.width;
        this->line = c.line;
        this->value = c.value;
        this->realV = c.realV;
        this->id = c.id;
        this->type = c.type;
        this->rrealv = c.rrealv;
        this->falselist = c.falselist;
        this->truelist = c.truelist;
        this->nextlist = c.nextlist;
        this->quad = c.quad;
	}
    void setFid(int fid)
    {
        id = fid;
    }
};


class oneWord
{
public:
    std::string type;
    std::string name;
    std::string value;

    int offset;
    oneWord(std::string type, std::string name, std::string value, int offset)
    {
        this->name = name;
        this->type = type;
        this->offset = offset;
        this->value = value;
    }
};
class sym_tbl
{
    std::string tblName;
    std::string nextTblName;
    sym_tbl* next_table;
    std::vector<oneWord> syms;
public:
    sym_tbl(std::string tblName )
    {
        this->tblName = tblName;
    //	this->nextTblName = nextTblName;
        //this->next_table = next_table;
    }
    void addsys(oneWord x)
    {
        syms.push_back(x);
    }
    std::string newTemp(std::string type, std::string value);

    oneWord lookup(std::string name)
    {

        for (auto ite = syms.begin(); ite != syms.end(); ite++) {
            //std::cout << ( * ite).name << std::endl;
            if ((*ite).name == name) {
                return *ite;
            }
        }
        return oneWord("None","None","None",-1);
    }

};
//-----------------------------------


struct Quaternion
{
    std::string type;
    std::string a;
    std::string b;
    // int addr=INIT_STATE;//init_state
    std::string addr = "INIT_STATE";//init_state
    Quaternion(std::string type, std::string a, std::string b, std::string addr) :type(type), a(a), b(b), addr(addr) {};
    Quaternion() { addr = "INIT_STATE"; };
};


class Parser
{
public: 

	void read_grammer(const std::string path);
	void read_grammer_Yacc(const std::string path);
	
//	std::vector<std::vector<generator>> generators_list;
	void get_symbol_first(const symbol & a);
	void get_all_symbol_first();
	void get_sequence_first(const std::vector<std::string>& seq, std::vector<std::string>& re);
	void get_item_group_list();
	void state_group_go(const _item_group_& scr, _item_group_& dst, std::string input);

	std::set<symbol> non_terminators;
	std::set<symbol> terminators;
	std::set<symbol> symbols;
	std::vector<std::vector<generator>> generators_list;  // each unit represent the generators whose left symbol is the same one, we set this structure to create first set conveniently
	std::vector<generator> pure_generator_list;    // contains every generators in order;
	
	std::set<_item_group_> _item_groups_;
	//each map represents the actions an item_group will take meeting diffrent symbols 
	//the vector means the different item_groups
	std::vector < std::map<std::string, int>> go_map;


	std::stack<int> itemS;// item state
	std::stack<word> symbolS;//

    //semantic actions
    std::tuple<word, std::string>(*p[229])();//pointer of semantic function
    void init();
    //

	void get_LR1_table();
	void print_LR1_table();
	void print_DFA();

	void get_state_group_list();

	void construct_closure(_item_group_& group);
	int check(const std::string path);
	int read_cache();


private:

	unsigned int num_termi = 0;
	unsigned int num_nontermi = 0;
	std::vector < std::pair<std::map<std::string, int>, std::map<std::string, int>>> table;
	std::vector< movement> LR1_table;

	std::map<std::string, std::set<symbol>> symbol2first;

	void make_cache();


};


