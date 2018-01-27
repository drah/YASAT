#include "parser.h"
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <algorithm>
#include <vector>
#include <deque>
#include <fstream>
#define NOT_ASSIGNED 0
#define NO_ANTEC -1
#define CLAUSE_SIZE_LIMIT 6
#define IS_DECISION 1
#define IS_IMPLICATION 0
#define FLIPPED 1
#define UNFLIPPED 0
#define RES_LIMIT 30
#define RESTART_CHANCE 500
using namespace std;

struct twolit{
    unsigned wl1;
    unsigned wl2;
    twolit():wl1(0),wl2(1){;}
    twolit(unsigned i, unsigned j):wl1(i),wl2(j){;}
};

struct decision{
    int *dec;
    int *var;
    int *level;
    int *antec;
    decision(int *a, int *b, int *c, int *d):dec(a),var(b),level(c),antec(d){;}
    ~decision(){;}
};

struct vs{
    int var;
    int *score;
    vs(int a, int *b):var(a),score(b){;}
    ~vs(){;}
};

class sat{
public:
    sat(vector<vector<int> >&, int);
    void print_info();
    bool solve();
    void write_result(char*);
private:
    void _assign(int, int, int, int, int);
    void _update_watch(int, bool);
    bool _verify();
    static bool _score_cmp(vs &a, vs &b){return (*a.score) < (*b.score);}
    void _restart();
    bool _preproc();
    bool _branch();
    bool _bcp(vector<int>*);
    int _analyze_conflict(); // return blevel
    void _resolve(vector<int>&, vector<int>&, int);
    void _backtrack(int);
    int _level;
    vector<int> *_to_bcp_clauses;
    vector<int> _null_clauses;
    int _conflicting_clause;
    int _conflicting_var;
    bool _solved;
    int _restart_chance;
    vector<vector<int> > _clauses;
    vector<twolit> _watch;
    vector<int> _vars;
    vector<vector<int> > _pos;
    vector<vector<int> > _neg;
    vector<int> _is_decisions;
    vector<int> _levels;
    vector<int> _orders;
    vector<int> _antecs;
    vector<int> _scores;
    vector<int> _flippeds;
    deque<decision> _decisions;
    vector<vs> _var_heap;
};

sat::sat(vector<vector<int> > &clauses, int maxVarIndex):_clauses(clauses),_level(0),_solved(false), _restart_chance(RESTART_CHANCE){
    srand(time(NULL));
    _watch.resize(_clauses.size());
    unsigned size = maxVarIndex + 1; // index 0 not used so plus 1
    _vars.resize(size, NOT_ASSIGNED);
    _is_decisions.resize(size);
    _levels.resize(size);
    _orders.resize(size);
    _antecs.resize(size);
    _scores.resize(size);
    _flippeds.resize(size, UNFLIPPED);
    _pos.resize(size);
    _neg.resize(size);
    for(unsigned c=0; c<_clauses.size(); c++){
        for(unsigned i=0; i<_clauses[c].size(); i++){
            int var = _clauses[c][i];
            int var_idx = abs(var);
            if(var > 0)
                _pos[var_idx].push_back(c);
            else
                _neg[var_idx].push_back(c);
	    _scores[var_idx] += 2;
        }
    }
    for(unsigned v=1; v<size; v++){
        _var_heap.push_back(vs(v, &_scores[v]));
    }
}

void sat::_assign(int var_idx, int var, int level, int antec, int is_decision){
    _vars[var_idx] = var;
    _is_decisions[var_idx] = is_decision;
    _levels[var_idx] = level;
    _antecs[var_idx] = antec;
    _orders[var_idx] = _decisions.size();
    if(level==0)
        _decisions.push_front(decision(&_is_decisions[var_idx], &_vars[var_idx], &_levels[var_idx], &_antecs[var_idx]));
    else
        _decisions.push_back(decision(&_is_decisions[var_idx], &_vars[var_idx], &_levels[var_idx], &_antecs[var_idx]));
    _update_watch(var_idx, var > 0);
}

void sat::_update_watch(int var_idx, bool assigned_pos){
    // go through the pos or neg, search not assigned lit in clauses
    vector<int> *pos_neg = assigned_pos ? &_neg[var_idx] : &_pos[var_idx];
    for(unsigned i=0; i<pos_neg->size(); i++){
        int c = pos_neg->at(i);
        unsigned *to_move;
        unsigned *another;
        if(abs(_clauses[c][_watch[c].wl1]) == var_idx){
            to_move = &_watch[c].wl1;
            another = &_watch[c].wl2;
        }
        else if(abs(_clauses[c][_watch[c].wl2]) == var_idx){
            to_move = &_watch[c].wl2;
            another = &_watch[c].wl1;
        }
        else continue;
        unsigned clause_size = _clauses[c].size();
        unsigned j = (*to_move + 1) % clause_size;
        while(j != *to_move){
            if(j != *another && _vars[abs(_clauses[c][j])] != -_clauses[c][j]){
                *to_move = j;
                break;
            }
            j = (j + 1) % clause_size;
        }
    }
}
void sat::_restart(){
    while(!_decisions.empty())
        _decisions.pop_back();
    while(!_var_heap.empty())
        _var_heap.pop_back();
    for(unsigned i=1; i<_vars.size(); i++){
        _vars[i] = NOT_ASSIGNED;
        _var_heap.push_back(vs(i, &_scores[i]));
    }
    printf("restart...%d chances remains\n", _restart_chance);
}

bool sat::solve(){
    int back_count = 0; 
    if(!_preproc())
        return false;
    while(1){
        if(back_count == 100 && _restart_chance > 0){
            _restart();
            back_count = 0;
            _restart_chance --;
            if(!_preproc())
                return false;
        }
        if(_restart_chance == 0)
            make_heap(_var_heap.begin(), _var_heap.end(), _score_cmp);
        if(!_branch())
            return true;
        while(!_bcp(_to_bcp_clauses)){
            int back_level = _analyze_conflict();
            if(back_level == -1) return false;
            _backtrack(back_level);
            back_count ++;
        }
    }
}

bool sat::_preproc(){
    // find length 1 clause, make heap according to score
//printf("In preproc: \n");
    for(unsigned i=0; i<_clauses.size(); i++){
        if(_clauses[i].size() == 1){
            int var = _clauses[i][0];
            int var_idx = abs(var);
            if(_vars[var_idx] == NOT_ASSIGNED){
                _watch[i].wl2 = 0;
                _assign(var_idx, var, 0, NO_ANTEC, IS_DECISION);
//printf("clause %d: %d, assign %d\n", i, _clauses[i][0], var);
                _to_bcp_clauses = var > 0 ? &_neg[var_idx] : &_pos[var_idx];
                if(_bcp(_to_bcp_clauses) == false)
                    return false;
            }
            else if(_vars[var_idx] == -var){
//printf("clause %d: %d, want to assign %d, but has %d\n", i, _clauses[i][0], var, _vars[var_idx]);
                return false;
            }
            else ;
        }
    }
    return true;
}

bool sat::_branch(){
    // pick 1 NOT_ASSIGNED var
    int var_idx;
    do {
        if(_var_heap.empty())
            return false;
        var_idx = _var_heap.front().var;
        pop_heap(_var_heap.begin(), _var_heap.end(), _score_cmp); _var_heap.pop_back();
    } while(_vars[var_idx] != NOT_ASSIGNED);
    // assign a rand value
    bool assigned_pos = (bool)(rand() % 2);
    int var = assigned_pos ? var_idx : -var_idx;
    _assign(var_idx, var, ++_level, NO_ANTEC, IS_DECISION);
//printf("assign %d at level %d\n", var, _level);
    _to_bcp_clauses = assigned_pos ? &_neg[var_idx] : &_pos[var_idx];
    return true;
}


bool sat::_bcp(vector<int> *clauses){
    vector<int> to_bcp_clauses = *clauses;
    for(unsigned i=0; i<to_bcp_clauses.size(); i++){
        int c = to_bcp_clauses[i];
        int var1 = _clauses[c][_watch[c].wl1];
        int var2 = _clauses[c][_watch[c].wl2];
        int var_idx1 = abs(var1);
        int var_idx2 = abs(var2);
        bool clause_has_only_one_lit = _clauses[c].size() == 1;
        bool got_unit_clause =  clause_has_only_one_lit || _vars[var_idx1] == -var1 || _vars[var_idx2] == -var2;
        if(!clause_has_only_one_lit && _vars[var_idx2] == -var2){
            swap(var1, var2);
            swap(var_idx1, var_idx2);
        }
        if(got_unit_clause){
            if(_vars[var_idx2] == NOT_ASSIGNED){
                if(clause_has_only_one_lit){
                    _assign(var_idx2, var2, 0, c, IS_IMPLICATION);
//printf("(bcp)clause has only one lit: assign %d at level 0\n", var2);
                }
                else {
                    _assign(var_idx2, var2, _level, c, IS_IMPLICATION);
//printf("(bcp)assign %d at level %d\n", var2, _level);
                }
                vector<int> *clauses_to_add = var2 > 0 ? &_neg[var_idx2] : &_pos[var_idx2];
                for(unsigned j=0; j<clauses_to_add->size(); j++){
                    to_bcp_clauses.push_back(clauses_to_add->at(j));
                }
            }
            else if(_vars[var_idx2] == -var2 && _vars[var_idx1] == -var1){ // Conflicting
                _conflicting_clause = c;
                _conflicting_var = var_idx2;
/*printf("conflicting:\n");
for(unsigned j=0; j<_clauses[c].size(); j++)
    printf("%d ", _clauses[c][j]);
printf("want to assign %d but has %d\n", var2, _vars[var_idx2]);
*/
                return false;
            }
            else ;
        }
    }
    return true;
} 

int sat::_analyze_conflict(){
//printf("In analyze:\n");
    int cur_level_count = 1;
    int cc = _conflicting_clause;
    int cv = _conflicting_var;
    vector<int> C = _clauses[cc];
    for(unsigned i=0; i<C.size(); i++){
        if(_levels[abs(C[i])] == _level && abs(C[i]) != cv)
            cur_level_count ++;
        if(cur_level_count > 1)
            break;
    }
    // 1UIP
    bool learnt = false;
    int res_count = 0;
    while(cur_level_count > 1 && res_count < RES_LIMIT){
        res_count ++;
/*printf("C=");
for(unsigned i=0; i<C.size(); i++)
  printf("%d ", C[i]);
printf("\n");
*/
        int p = 0;
        int p_order = -1;
        for(unsigned i=0; i<C.size(); i++){
            int var_idx = abs(C[i]);
            if(_orders[var_idx] > p_order && _levels[var_idx] == _level){
                p = var_idx;
                p_order = _orders[p];
            }
        }
//printf("p=%d\n", p);
        if(_antecs[p] == NO_ANTEC)
            break;
        _resolve(C, _clauses[_antecs[p]], p);
        learnt = true;

        cur_level_count = 0;
        for(unsigned i=0; i<C.size(); i++){
            if(_is_decisions[abs(C[i])] == IS_IMPLICATION)
                cur_level_count ++;
        }
        if(cur_level_count == 1)
            break;

        cur_level_count = 0;
        for(unsigned i=0; i<C.size(); i++){
            if(_levels[abs(C[i])] == _level)
                cur_level_count ++;
            if(cur_level_count > 1)
                break;
        }
    }
    // add the learnt clauses
/*
printf("Learnt clause: ");
for(unsigned i=0; i<C.size(); i++){
    printf("%d ", C[i]);
}
printf("\n");
*/
    if(learnt){
        if(C.size() <= CLAUSE_SIZE_LIMIT){
            int c = _clauses.size();
            _clauses.push_back(C);
            if(C.size() == 1)
                _watch.push_back(twolit(0, 0));
            else
                _watch.push_back(twolit(0, 1));
            for(unsigned i=0; i<C.size(); i++){
                if(C[i] > 0)
                    _pos[abs(C[i])].push_back(c);
                else
                    _neg[abs(C[i])].push_back(c);
            }
        }
        // add the score
        for(unsigned i=0; i<C.size(); i++){
            _scores[abs(C[i])] += 3;
        }
        // get the back level
        int back_level = 0;
        for(unsigned i=0; i<C.size(); i++){
            int var_idx = abs(C[i]);
            if(_levels[var_idx] != _level 
              && _levels[var_idx] > back_level 
              && _is_decisions[var_idx] == IS_DECISION 
              && _flippeds[var_idx] == UNFLIPPED){
                back_level = _levels[var_idx];
            }
        }
        return back_level;
    }
    // simple backtrack
    else {
        int back_level = _level - 1;
        // if(_level < 0) _level = 0;
        return back_level;
    }
}

void sat::_resolve(vector<int> &C, vector<int> &antec, int p){
    for(unsigned i=0; i<C.size(); i++){
        if(abs(C[i]) == p){
            C.erase(C.begin()+i);
            break;
        }
    }
    for(unsigned i=0; i<antec.size(); i++){
        if(abs(antec[i]) != p){
            bool not_in = true;
            for(unsigned j=0; j<C.size(); j++){
                if(C[j] == antec[i]){
                    not_in = false;
                    break;
                }
            }
            if(not_in)
                C.push_back(antec[i]);
        }
    }
}

void sat::_backtrack(int level){
//printf("In backtrack: \n");
    // score decay
    for(unsigned i=1; i<_scores.size(); i++)
        _scores[i] --;
    // pop decisions to level, score decay, learnt score, push to _var_heap
    while(!_decisions.empty()){
        decision d = _decisions.back();
        int var_idx = abs(*d.var);
        if(*d.level >= level){
            _decisions.pop_back();
            *d.var = NOT_ASSIGNED;
            _flippeds[var_idx] = UNFLIPPED;
            _var_heap.push_back(vs(var_idx, &_scores[var_idx]));
            push_heap(_var_heap.begin(), _var_heap.end(), _score_cmp);
        }
        else break;
    }
    _to_bcp_clauses = &_null_clauses;
    _level = level;
//printf("back to level %d\n", _level);
}

void sat::print_info(){
    printf(" [ clauses and watch: ]\n");
    for(unsigned i=0; i<_clauses.size(); i++){
        for(unsigned j=0; j<_clauses[i].size(); j++){
            printf("%d ", _clauses[i][j]);
        }
        printf("watch %d %d \n", _watch[i].wl1, _watch[i].wl2);
    }
    printf("\n [ var-value-score-pos-neg: ]\n");
    for(unsigned i=1; i<_vars.size(); i++){
        printf("%d %d %d pos: ", i, _vars[i], _scores[i]);
        for(unsigned j=0; j<_pos[i].size(); j++)
            printf("%d ", _pos[i][j]);
        printf("neg: ");
        for(unsigned j=0; j<_neg[i].size(); j++)
            printf("%d ", _neg[i][j]);
        printf("\n");
    }
    printf("\n [ var_score heap: ]\n");
    for(unsigned i=0; i<_var_heap.size(); i++)
        printf("var %d score %d\n", _var_heap[i].var, *_var_heap[i].score);
}

bool sat::_verify(){
    for(unsigned c=0; c<_clauses.size(); c++){
        bool clause_check = false;
        for(unsigned i=0; i<_clauses[c].size(); i++){
            int clause_var = _clauses[c][i];
            int var = _vars[abs(clause_var)];
            if(var == clause_var){
                clause_check = true;
                break;
            }
        }
        if(!clause_check)
            return (_solved = false);
    }
    return (_solved = true);
}

void sat::write_result(char* filename){
    _verify();
    int len = strlen(filename);
    filename[len-3] = 's'; filename[len-2] = 'a'; filename[len-1] = 't';
    ofstream fout(filename);
    if(_solved){
        fout << "s SATISFIABLE\nv ";
        for(unsigned i=1; i<_vars.size(); i++)
            fout << _vars[i] << ' ';
        fout << "0\n";
        printf("YA\n");
    }
    else{
        fout << "s UNSATISFIABLE\n";
        printf("NO\n");
    }
    fout.close();
}

int main(int argc, char* argv[]){
    vector<vector<int> > clauses;
    int maxVarIndex;
    parse_DIMACS_CNF(clauses, maxVarIndex, argv[1]);
    sat solver(clauses, maxVarIndex);
    solver.solve();
    solver.write_result(argv[1]);
    return 0;
}
