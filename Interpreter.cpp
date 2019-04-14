#include <bits/stdc++.h>
#define lex first
#define num second

using namespace std;

pair<string, int> cur = {"lol", -1}, nextt = {"lol", -1};
int linec, linen;
bool chk, cyc = 0, en = 0;
string typ;
pair<string, int> com[10000]; ///стек для операций
int ind = 0;///текущий top в стеке
stack<pair<string, int> > pol;///разбор полиза
FILE *fp;

void get_lex() { ///считывание лексемы
    int aba = ftell(fp);
    fseek(fp, 0, SEEK_END);
    if(ftell(fp) == aba) {
        en = 1;
        cur = nextt;
        return;
        //throw (string) "You've missed smth.\n";
    }
    fseek(fp, aba, SEEK_SET);
    string a;
    int b;
    char l;
    fscanf(fp, "%c", &l);
    cout << l << "    get_lex_l\n";
    if(l == ' ') {
        cout << "UJAS\n";
        a += l;
    }
    while(l != ' ' && l != '\n') {
        a += l;
        fscanf(fp, "%c", &l);
    }
    //cout << a << "    get_lex_a\n";
    //fscanf(fp, "%c", &l);
    fscanf(fp, "%d", &b);
    cout << b << "     get_lex -> b\n";
    fscanf(fp, "%c", &l);
    //cin >> a >> b;
    linec = linen;
    fscanf(fp, "%d\n", &linen);
    cout << linen << "  get_lex -> linen\n";
    cur.lex = nextt.lex;
    cur.num = nextt.num;
    nextt = {a, b};
}

void S(); ///start - главная функция
void con();
void atom();
void atom1();
void des();
void elem();
void elem_list();
void expr();
void expr1();
void log_def();
bool oper();
void oper_dowhile();
void oper_for();
bool oper_enter();
bool oper_expr();
void section();
void sim_exp();
bool sost_oper();
void spec_atom();
bool spets_oper();
void term();
void intepreter();
void fun();
int per(string s);

struct tid{
    string name;
    string type;
    string znach;
};

int level = -1;
vector<vector<vector<tid> > > obl_vid;
///каждый раз, когда видим открывающую фиг скобку - новый тид
///закрывающая - тид удаляется
void in_des(string tp) { ///должна быть в try блоке ///похоже не дичь
    for(int j = 0; j < obl_vid[level][obl_vid[level].size() - 1].size(); j++) {
        if(obl_vid[level][obl_vid[level].size() - 1][j].name == cur.lex) {
            throw (string)"You have already described the variable.\n";
        }
    }
    //cout << cur.lex << " in_des_cur\n";
    tid now;
    now.name = cur.lex;
    now.type = tp;
    obl_vid[level][obl_vid[level].size() - 1].push_back(now);
}

struct tri {
    int f, s, t;
};
tri tid_ser(string s) {
    for(int i = level; i >= 0; i--) {
        for(int j = obl_vid[i].size() - 1; j >= 0; j--) {
            for(int h = 0; h < obl_vid[i][j].size(); h++) {
                if(obl_vid[i][j][h].name == s) {
                    tri a;
                    a.f = i; a.s = j; a.t = h;
                    return a;
                }
            }
        }
    }
}

stack<string> st; ///стек для соответствия типов
void check_id() { ///при использовании переменной
    for(int i = level; i >= 0; i--) {
        for(int j = obl_vid[i].size() - 1; j >= 0; j--) {
            for(int h = 0; h < obl_vid[i][j].size(); h++) {
      //          cout << obl_vid[i][j][h].name << " " << i << " " << j << " " << h << " " << cur.lex << " check_id\n";
                if(obl_vid[i][j][h].name == cur.lex) {
                    st.push(obl_vid[i][j][h].type);
                    return;
                }
            }
        }
    }
    throw (string)"There is no description for the variable.\n";
}
void check_op() { ///при использовании переменной
    string t1, t2, op, t, r;
    //cout << st.top() << " " << st.size() << " check_op\n";
    t1 = st.top();
    st.pop();
    //cout << st.top() << " " << st.size() << " check_op\n";
    op = st.top();
    st.pop();
    //cout << st.top() << " " << st.size() << " check_op\n";
    t2 = st.top();
    st.pop();
    if(op == "+" || op == "-" || op == "*" || op == "/" || op == "%" || op == "^") {
        r = "int";
        t = "int";
    }
    if(op == "&&" || op == "||") {
        r = "bool";
        t = "bool";
    }
    if(op == ">" || op == "<" || op == "==") {
        r = "bool";
        t = t1;
    }
    if(t1 == t2 && t == t1) {
        st.push(r);
    } else {
        throw (string)"Type mismatch.\n";
    }
    //cout << st.top() << " " << st.size() << " check_op\n";
}
void check_not() {
    if(st.top() == "bool") {
        st.pop();
        st.pop();
        st.push("bool");
    } else {
        throw (string) "Type mismatch.\n";
    }
}
void eq_type(/*string t1*/) {
    string t1, t2, op;
    //cout << st.top() << " " << st.size() << " EQ_TYPE\n";
    t1 = st.top();
    st.pop();
    //cout << st.top() << " " << st.size() << " EQ_TYPE\n";
    op = st.top();
    st.pop();
    //cout << st.top() << " " << st.size() << " EQ_TYPE\n";
    t2 = st.top();
    st.pop();
    if(t1 == t2) {
        st.push(t1);
    } else {
        throw (string)"Type mismatch.\n";
    }
    //cout << st.top() << " " << st.size() << " EQ_TYPE\n";
}
void eq_bool(/*string t1*/) {
    string t1;
    t1 = st.top();
    st.pop();
    if(t1 == "bool") {
        st.push(t1);
    } else {
        throw (string)"Type mismatch.\n";
    }
}
int sti(string s) {
    int a = 0;
    for(auto i : s) {
        a *= 10;
        a += (i - '0');
    }
    return a;
}

string its(int a) {
    string s;
    if(!a) {
        return "0";
    }
    while(a) {
        s = char(a % 10 + '0') + s;
        a /= 10;
    }
    return s;
}

bool oper_if() {
    cout << cur.lex << " " << cur.num << " oper_if\n";
    if(cur.lex == "if") {
        get_lex();
        if(cur.lex == "(") {
            get_lex();
            chk = 1;
            expr();
            if(!chk) {
                throw (string) "Expected expression.\n";
            }
            eq_bool();
            int ie = ind;
            auto x = cur;
            x.lex = "p" + its(ind);
            x.num = 8;
            com[ind] = x;
            ind++;
            if(cur.lex == ")") {
                get_lex();
                if(!oper()) {
                    throw (string) "Expected operator.\n";
                }
                com[ie].lex = "p" + its(ind);
                return 1;
            } else {
                throw (string) "Expected ).\n";
            }
        } else {
            throw (string) "Expected (.\n";
        }
    } else {
        return 0;
    }
}
void con() {/// константа
    int yyy = 0;
    if(cur.lex == "+" || cur.lex == "-") {  ///го просто запомним знак, и если минус домножим на -1 сонце
        if(cur.lex == "-")
            yyy = 1;
        get_lex();
        if(cur.num == 7 && cur.lex[0] >= '0' && cur.lex[0] <= '9') {
            if(yyy)
                {st.push("int");
                cur.lex = '-' + cur.lex;}
            else
                st.push("int");
            auto x = cur;
            if(nextt.lex == ".") {
                get_lex();
                get_lex();
                if(cur.lex[0] < '0' || cur.lex[0] > '9') {
                    throw (string) "Expected number.\n";
                }
                x.lex += '.' + cur.lex;
            }
            com[ind] = x;
            ind++;
            get_lex();
        } else {
            throw (string) "Expected number.\n";
        }
    } else if(cur.num == 7 && cur.lex[0] >= '0' && cur.lex[0] <= '9') {
        //cout << cur.lex << " " << nextt.lex << " constanta\n";
        st.push("int");
        auto x = cur;
        if(nextt.lex == ".") {  ///тут капец с дробными числами блин
            get_lex();
            get_lex();
            if(cur.lex[0] < '0' || cur.lex[0] > '9') {
                throw (string) "Expected number.\n";
            }
            x.lex += '.' + cur.lex;
        }
        com[ind] = x;
        ind++;
        get_lex();
      //  cout << cur.lex << " in_con_lex\n";
    } else {
        //cout << "AGA\n";
        //cout << "con_throw\n";
        throw (bool) 0;
    }
}

void log_def() { /// логическое значение
    if(cur.lex == "true" || cur.lex == "false") {
        st.push("bool");
        com[ind] = cur;
        ind++;
        get_lex();
    } else {
        //cout << "log_throw\n";
        throw (bool) 0;
    }
}

void spec_atom() { ///спец. атом
    //cout << cur.lex << " " << nextt.lex << " spec_atom\n";
    if(cur.lex == "!") {
        get_lex();
        atom();
        check_not();
        com[ind] = cur;
        ind++;
    } else {
        try {
            con();
        }
        catch(bool x) {
      //      cout << "spec_atom -> con_catch -> log_def\n";
            log_def();
        }
    }
}
void atom() { ///атом
    //cout << cur.lex << " " << nextt.lex << " atom\n";
    if(cur.num == 2) {
        check_id();
        auto x = tid_ser(cur.lex);
        string np = '~' + its(x.f) + '&' + its(x.s) + '&' + its(x.t);
        com[ind].lex = np;
        com[ind].num = cur.num;
        ind++;
      //  cout << "atompomogiti\n";
        //cout << "atompomogiti\n";
        get_lex();
    } else if(cur.lex == "(") {
        get_lex();
        chk = 1;
        expr();
        if(!chk) {
            throw (string) "Expected expression.\n";
        }
        if(cur.lex != ")") {
            throw (string) "Expected ) after the expression.\n";
        }
        get_lex();
    } else {
        try{
            spec_atom();
        }
        catch(bool x) {
        //    cout << "atom_throw\n";
            throw (bool) 0;
        }
    }
}
void atom1() {///атом 1
    //cout << cur.lex << " " << nextt.lex << " atom1\n";
    try {
        atom();
    }
    catch(bool x) {
        //cout << "VI\n";
      //  cout << "atom1_throw\n";
        throw (bool) 0;
    }
    //cout << cur.lex << " atom1\n";
    if(cur.lex == "^") {
        auto x = cur;
        st.push(cur.lex);
        get_lex();
        atom();
        check_op();
        com[ind] = x;
        ind++;
    } else if(cur.lex == "++" || cur.lex == "--") {///операнды инт
        if(st.top() != "int") {
            throw (string) "Expected int value before increment.\n";
        }
        cout << "atom1 -> ++\n";
        com[ind] = cur;
        ind++;
        get_lex();
    }
}
void term() {///терм
    //cout << cur.lex << " " << nextt.lex << " term\n";
    try {
        atom1();
    }
    catch(bool x) {
      //  cout << "term_throw\n";
        throw (bool) 0;
    }
 //   st.push(cur.lex);
    while(cur.lex == "*" || cur.lex == "/" || cur.lex == "&&" || cur.lex == "%") {
        auto x = cur;
        st.push(cur.lex);
        get_lex();
        atom1();
        check_op();
        com[ind] = x;
        ind++;
    }
}
void sim_exp() {///простое выражение
    //cout << cur.lex << " " << nextt.lex << " simexp\n";

    try {
        term();
    }
    catch(bool x) {
        throw (bool) 0;
    }
    while(cur.lex == "+" || cur.lex == "-" || cur.lex == "||") {
        auto x = cur;
        st.push(cur.lex);
        get_lex();
        term();
        check_op();
        com[ind] = x;
        ind++;
    }
}

void expr1() {///выражние 1
    //cout << cur.lex << " " << nextt.lex << " expr1\n";
    /// добавить сюда ловушку неправильного!!!!!
    try {
        sim_exp();
    }
    catch(bool x) {
      //  cout << "sim_exp_throw\n";
        chk = 0;
        throw (bool) 0;
    }
    while(cur.lex == ">" || cur.lex == "<" || cur.lex == "!=" || cur.lex == "<=" || cur.lex == ">=" || cur.lex == "==") {
        auto x = cur;
        st.push(cur.lex);
        get_lex();
        expr1();
        check_op();
        com[ind] = x;
        ind++;
    }
}
void expr() { ///выражение
    //cout << cur.lex << " " << nextt.lex << " expr\n";
    if(cur.num == 2 && nextt.lex == "=") {
        check_id();
        auto x = tid_ser(cur.lex);
        string np = '~' + its(x.f) + '&' + its(x.s) + '&' + its(x.t);
        com[ind].lex = np;
        com[ind].num = cur.num;
        ind++;
        get_lex();
      //  cout << cur.lex << " " << nextt.lex << " expr_inname_getlex\n";
        if(cur.lex == "=") {
            auto x = cur;
            st.push(cur.lex);
            get_lex();
            expr();
            eq_type();
            com[ind] = x;
            ind++;
        } else {
            //chk = false;
            throw (string) "Expected = after the name.\n";
        }
    } else {
        try {
            expr1();
        //    cout << "sdfsdfsdsdfsdfsdfsdfsdfsdfsdfsdf";
          //  eq_type();
          //  cout << "ASDASDASD";
        }
        catch(bool x) {
            //cout << "expr_throw\n";
            chk = false;
            //throw 0;
        }
    }
}

bool oper_expr() {
        chk = true;
        expr();
        if(!chk) {
            //cout << "oper_expr\n";
            return 0;
        } else {
            if(cur.lex != ";") {
                return 0;
            }
            get_lex();
            return 1;
        }
}

void elem() {
    cout << cur.lex << " " << nextt.lex << " elem\n";
    if(cur.lex == "<<") {
        auto x = cur;
        get_lex();
        cout << cur.lex << " " << nextt.lex << " elem -> get_lex\n";
        chk = 0;
        //cout << cur.lex << " " << nextt.lex << " elem_afterexpr\n";
        if(cur.lex == "endl") { ///CHECK11111111111111111111111111111111111111111111111111111
          //  cout << cur.lex << " " << nextt.lex << " elem_endl\n";
            auto pik =  cur;
            pik.lex = "\n";
            pik.num = 7;
            cout << pik.num << " piki_num_figa_vam\n";
            com[ind] = pik;
            ind++;
            get_lex();
            chk = 1;
        } else if(cur.lex[0] == '\"' && nextt.num == 7) { ///CHECK11111111111111111111111111111111111111111111111111111
            cout << "HERE\n";
            get_lex();
            auto pik = cur;
            get_lex();
            get_lex();
            pik.num = 7;
            com[ind] = pik;
            ind++;
            chk = 1;
            //cout << cur.lex << " " << nextt.lex << " elem_const\n" << chk;
        }
        if(!chk) {
            chk = 1;
            expr();
            cout << chk << "\n";
        }
        com[ind] = x;
        ind++;
        if(!chk) {
            throw (string) "Expected smth after <<.\n";
        }
    } else if(cur.lex == ">>") {
        auto x = cur;
        get_lex();
        if(cur.num == 2) {
            check_id();
            st.pop();
            auto p = tid_ser(cur.lex);
            com[ind].lex = "~" + its(p.f) + "&" + its(p.s) + "&" + its(p.t);
            com[ind].num = 2;
            ind++;
            com[ind] = x;
            ind++;
            get_lex();
        } else {
            throw (string) "Expected name after >>.\n";
        }
    } else {
        chk = 0;
    }
}

void elem_list(){ /// список элементов
    chk = 1;
    elem();
    if(!chk) {
        throw (string) "Expected << or >>.\n";
    }
    chk = 1;
    while(chk) {
        cout << "elem_list -> whilechk\n";
        elem();
    }
}

bool oper_enter() {
    //get_lex();
    cout << cur.lex << " " << nextt.lex << " oper_enter\n";
    if(cur.lex == "cinout"){
        get_lex();
        //cout << "COOL\n";
        elem_list();
        if(cur.lex != ";") {
            throw (string)"Expected ; after operator\n";
        }
        get_lex();
        return 1;
    }
    else {
        //cout << "oper_enter\n";
        return 0;
    }
}
int beg = 0;
bool sost_oper() { ///Оля - кек, хорошо, Оля. Надо изменить if на while.
    cout << cur.lex << " " << nextt.lex << " sost_oper\n";
    if(cur.lex != "{") {
        cout << "YES\n";
        return 0;
    }
    if(obl_vid.size() <= level + 1) {
        vector<vector<tid> > p;
        obl_vid.push_back(p);
    }
    level++;
    //vector<tid> v;
    obl_vid[level].push_back(vector<tid> ());
    cout << "sost_oper_new_obl_vid\n";
    get_lex();
    while(oper()) {
        cout << "LOL\n";
        cout << cur.lex << " " << nextt.lex << " sost_operrrrrr\n";
    }
    cout << cur.lex << " " << nextt.lex << " soper\n";
    if(cur.lex != "}") {
        return 0;
    }
    level--;
    //intepreter();
    //pol.clear();
    //beg = ind;
    //obl_vid[level].pop_back();
    cout << "sost_oper_del_obl_vid\n";
    get_lex();
    return 1;
}

void oper_for(){
    int ie2, ie3, pe2, qe2, ip; ///индекс начала второго выражения, индекс начала третьего, переход по условию, переход без условия, индекс переменной
    if(cur.lex == "(") {
        //cout << "in_oper_for\n";
        get_lex();
        cout << cur.lex << " " << nextt.lex << " oper_for_inbrackets\n";
        if(cur.num == 2 && nextt.lex == ":") {
            chk = 0;
        } else {
            chk = 1;
            expr();
        }
        cout << chk << " oper_for\n";
        if(!chk) {
            try {
                cout << "oper_for before des\n";
                //vector<vector<tid> > v;
                //obl_vid.push_back(v);
                //level++;
                des();
                chk = 1;
                ie2 = ind;
                expr();
                if(!chk) {
                    throw (string) "Expected expression.\n";
                }
                eq_bool();
                auto x = cur;
                x.lex = "p" + its(ind);
                x.num = 8;
                pe2 = ind;
                com[ind] = x;
                ind++;
                x.lex = "!" + its(ind);
                x.num = 8;
                qe2 = ind;
                com[ind] = x;
                ind++;
                if(cur.lex == ";") {
                    //cout << "AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAa\n";
                    get_lex();
                    chk = 1;
                    ie3 = ind;
                    expr();
                    if(!chk) {
                        throw (string) "Expected expression.\n";
                    }
                    auto x = cur;
                    x.lex = "!" + its(ie2);
                    x.num = 8;
                    com[ind] = x;
                    ind++;
                } else {
                    throw (string) "Expected ;.\n";
                }
                if(cur.lex == ")") {
                    get_lex();
                    cout << cur.lex << " " << nextt.lex << " oper_for_cfor_afterbrackets_checkoper\n";
                    com[qe2].lex = "!" + its(ind);
                    if(!oper()) {
                        throw (string) "Expected operator.\n";
                    }
                    auto x = cur;
                    x.lex = "!" + its(ie3);
                    x.num = 8;
                    com[ind] = x;
                    ind++;
                    com[pe2].lex = "p" + its(ind);
                } else {
                    throw (string) "Expected ).\n";
                }
            }
            catch(string s) {
                //level--;
                if(s == "Expected type in description.\n" || s == "LOL") {
                    if(cur.num == 2) {
                        check_id();
                        auto x = tid_ser(cur.lex);
                        ip = ind;
                        com[ind].lex = '~' + its(x.f) + '&' + its(x.s) + '&' + its(x.t);
                        com[ind].num = 2;
                        ind++;
                        get_lex();
                        if(cur.lex == ":" && nextt.lex == "=") {
                            get_lex();
                            get_lex();
                            st.push("=");
                        } else {
                            throw (string)"Expected := in pfor.\n";
                        }
                        try {
                            chk = 1;
                            expr();
                            if(!chk) {
                                throw true;
                            }
                            eq_type();
                            auto x = cur;
                            x.lex = "=";
                            x.num = 3;
                            com[ind] = x;
                            ind++;
                            if(cur.lex == "to" || cur.lex == "downto") {
                                bool v;
                                if(cur.lex == "to") {
                                    v = 0;
                                } else {
                                    v = 1;
                                }
                                ie2 = ind;
                                com[ind] = com[ip];
                                ind++;
                                get_lex();
                                chk = 1;
                                expr();
                                if(!chk) {
                                    throw true;
                                }
                                eq_type();
                                if(v) {
                                    com[ind].lex = ">";
                                    com[ind].num = 3;
                                    ind++;
                                } else {
                                    com[ind].lex = "<";
                                    com[ind].num = 3;
                                    ind++;
                                }
                                x = cur;
                                x.lex = "p" + its(ind);
                                x.num = 8;
                                pe2 = ind;
                                com[ind] = x;
                                ind++;
                                x.lex = "!" + its(ind);
                                x.num = 8;
                                qe2 = ind;
                                com[ind] = x;
                                ind++;
                                ie3 = ind;
                                com[ind] = com[ip];
                                ind++;
                                com[ind] = com[ip];
                                ind++;
                                com[ind].lex = "1";
                                com[ind].num = 7;
                                ind++;
                                if(v) {
                                    com[ind].lex = "-";
                                    com[ind].num = 3;
                                    ind++;
                                } else {
                                    com[ind].lex = "+";
                                    com[ind].num = 3;
                                    ind++;
                                }
                                x = cur;
                                x.lex = "=";
                                x.num = 3;
                                com[ind] = x;
                                ind++;
                                com[ind].lex = "!" + its(ie2);
                                com[ind].num = 8;
                                ind++;
                                if(cur.lex == ")") {
                                    get_lex();
                                    com[qe2].lex = "!" + its(ind);
                                    if(!oper()) {
                                        throw (string) "Expected operator.\n";
                                    }
                                    x = cur;
                                    x.lex = "!" + its(ie3);
                                    x.num = 8;
                                    com[ind] = x;
                                    ind++;
                                    com[pe2].lex = "p" + its(ind);
                                } else {
                                    throw (string) "Expected ).\n";
                                }
                            } else {
                                throw (string) "Expected to or downto.\n";
                            }
                        }
                        catch(bool x) {
                            throw (string) "Expected expression.\n";
                        }
                    } else {
                        throw (string) "Expected for grammar.\n";
                    }
                } else {
                    throw s;
                }
            }
        } else {
            if(cur.lex == ";") { ///выражение 2
                get_lex();
                chk = 1;
                ie2 = ind;
                expr();
                if(!chk) {
                    throw (string) "Expected expression.\n";
                }
                eq_bool();
                auto x = cur;
                x.lex = "p" + its(ind);
                x.num = 8;
                pe2 = ind;
                com[ind] = x;
                ind++;
                x.lex = "!" + its(ind);
                x.num = 8;
                qe2 = ind;
                com[ind] = x;
                ind++;
            } else {
                throw (string) "Expected ;.\n";
            }
            if(cur.lex == ";") {
                get_lex();
                chk = 1;
                ie3 = ind;
                expr();
                if(!chk) {
                    throw (string) "Expected expression.\n";
                }
                auto x = cur;
                x.lex = "!" + its(ie2);
                x.num = 8;
                com[ind] = x;
                ind++;
            } else {
                throw (string) "Expected ;.\n";
            }
            if(cur.lex == ")") {
                get_lex();
                com[qe2].lex = "!" + its(ind);
                if(!oper()) {
                    throw (string) "Expected operator.\n";
                }
                auto x = cur;
                x.lex = "!" + its(ie3);
                x.num = 8;
                com[ind] = x;
                ind++;
                com[pe2].lex = "p" + its(ind);
            } else {
                throw (string) "Expected ).\n";
            }

        }
    } else {
        throw (string) "Expected (.\n";
    }
}

bool spets_oper(){
    //get_lex();
    cout << cur.lex << " " << nextt.lex << "  beg_spets_oper\n";
    if(cur.lex == "for"){
        cout << cur.lex << " " << nextt.lex << "  spets_oper_linefor\n";
        get_lex();
        oper_for();
        if(cur.lex == "else") {
            get_lex();
            if(!oper()) {
                throw (string) "Expected operator.\n";
            }
        }
        return 1;
    }
    else
        if(cur.lex == "do"){
            get_lex();
            oper_dowhile();
            return 1;
        }
        else
            return 0;
}

void oper_dowhile() {
    int b = ind;
    if(!oper()) {
        throw (string) "Expected operator.\n";
    }
    cout << "oper_dowhile_afteroper\n";
    if(cur.lex == "while" && nextt.lex == "(") {
        cout << "NETUT\n";
        get_lex();
        get_lex();
        chk = 1;
        expr();
        if(!chk) {
            throw (string) "Expected expression.\n";
        }
        eq_bool();
        auto x = cur;
        x.lex = "p" + its(ind);
        x.num = 8;
        com[ind] = x;
        ind++;
        x.lex = "!" + its(b);
        x.num = 8;
        com[ind] = x;
        ind++;
        com[ind - 2].lex = "p" + its(ind);
        if(cur.lex != ")") {
            throw (string) "Expected ).\n";
        }
        cout << "NU NA**I\n";
        get_lex();
        cout << "NU NA**I\n";
        if(cur.lex != ";") {
            throw (string) "Expected ;.\n";
        }
        get_lex();
    } else {
        throw (string) "Wrong dowhile.\n";
    }
}
bool oper(){
    cout << cur.lex << " " << nextt.lex << "\n";
    bool c = 1;
    try {
        des();
    }
    catch(string s) {
        if(s == "LOL") {
            c = 0;
            cout << s << " ne des((((\n";
        } else {
            throw s;
        }
    }
    if(!(oper_expr() || oper_enter() || spets_oper() || c || sost_oper() || oper_if())) {
        cout << "Expected operator";
        return 0;
    } else{
        cout << " oper_else_return1\n";
        return 1;
    }
}

void section() { ///секция
    if(cur.num == 2) {
        in_des(typ);
        auto x = tid_ser(cur.lex);
        string np = '~' + its(x.f) + '&' + its(x.s) + '&' + its(x.t);
        com[ind].lex = np;
        com[ind].num = cur.num;
        ind++;
        get_lex();
        cout << cur.lex << " " << nextt.lex << " section_inname_getlex\n";
        //cout << cur.lex << "\n";
        if(cur.lex == "=") {
            auto x = cur;
            st.push(cur.lex);
            cout << st.top() << " " << st.size() << " stack!!!\n";
            get_lex();
            expr();
            eq_type();
            com[ind] = x;
            ind++;
            //cout << cur.lex << " section\n";
        }
        //cout << "section section\n";
        if(cur.lex == ",") {
            //cout << cur.lex << " sec\n";
            get_lex();
            //in_des(typ);
            cout << cur.lex << " sec\n";
            section();
        } else if(cur.lex == ";") {
            //get_lex();
            //cout << cur.lex << " section\n";
            return;
        } else {
            //cout << "throw section\n";
            throw (string) "Expected something else in description after the name.\n";
        }
    } else {
        throw (string)"Expected name in description.\n";
    }
}
void des() { ///описание
    if(cur.lex == "int" || cur.lex == "bool" || cur.lex == "double") {
        cout << cur.lex << " " << nextt.lex << " des_intype\n";
        typ = cur.lex;
        get_lex();
        st.push(typ);
        cout << cur.lex << " " << nextt.lex << " des_intype_getlex\n";
        //cout << cur.lex << " des\n";
        section();
        while(cur.lex == ",") {
            get_lex();
            cout << cur.lex << " " << nextt.lex << " deslol\n";
            section();
        }
        //cout << cur.lex << " " << nextt.lex << " deslol\n";
        if(cur.lex != ";") {
            string g = "Expected ; after the description.\n";
            throw g;
        }
        get_lex();
        //}
    } else {
        chk = 0;
        throw (string)"LOL";
    }
}
void S() { ///start - главная функция
    fp = fopen("leksems.txt", "r");
    get_lex();
    //cout << "working\n";
    get_lex();
    //cout << "working\n";
    //cout << cur.lex << " " << nextt.lex << "\n";
    if(cur.lex != "int" || nextt.lex != "main") {
        des();
        //cout << "working\n";
    }
    //cout << cur.lex << "\n";
    //cout << "working\n";
    if(cur.lex != "int") {
        //string g = "Expected int main() function.\n";
        throw (string)"Expected int main() function.\n";
    }
    get_lex();
    if(cur.lex != "main") {
        string g = "Expected int main() function.\n";
        throw g;
    }
    get_lex();
    if(cur.lex != "(") {
        string g = "Expected int main() function.\n";
        throw g;
    }
    get_lex();
    if(cur.lex != ")") {
        string g = "Expected int main() function.\n";
        throw g;
    }
    get_lex();
    if(!sost_oper()) {
        throw (string)"Error in operator.\n";
    }
    cout << "RSG\n";
    for(int i = 0; i < ind; i++) {
        cout << com[i].lex << " " << com[i].num << " " << i << "\n";
    }
    fclose(fp);
}

void fun(string s) { ///операция
    pair<string, int> a, b, c;
    if(s == "*"){ ///даблы! bool!!!!!!!!!!!!!!!!!!!!!!!!!!!
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        x.lex = its(f1 * f2);
        x.num = 7;
        pol.push(x);
    } else if(s == "/"){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        x.lex = its(f1 / f2);
        x.num = 7;
        pol.push(x);
    } else if(s == "+"){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        x.lex = its(f1 + f2);
        x.num = 7;
        pol.push(x);
    } else if(s == "-"){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        x.lex = its(f1 - f2);
        x.num = 7;
        pol.push(x);
    } else if(s == "++"){
        a = pol.top();
        pol.pop();
        int f1;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
            obl_vid[n][m][h].znach = its(sti(obl_vid[n][m][h].znach) + 1);
        }
        pol.push(a);
    } else if(s == "--"){
        a = pol.top();
        pol.pop();
        int f1;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
            obl_vid[n][m][h].znach = its(sti(obl_vid[n][m][h].znach) - 1);
        }
        pol.push(a);
    } else if(s == "!"){
        a = pol.top();
        pol.pop();
        bool f1;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        if(f1) {
            x.lex = "false";
        } else {
            x.lex = "true";
        }
        x.num = 7;
        pol.push(x);
    } else if(s == ">"){ ///only int
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        if(f1 > f2) {
            x.lex = "true";
        } else {
            x.lex = "false";
        }
        x.num = 7;
        pol.push(x);
    } else if(s == "<"){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        if(f1 < f2) {
            x.lex = "true";
        } else {
            x.lex = "false";
        }
        x.num = 7;
        pol.push(x);
    } else if(s == "=="){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        if(f1 == f2) {
            x.lex = "true";
        } else {
            x.lex = "false";
        }
        x.num = 7;
        pol.push(x);
    } else if(s == "="){
        //cout << "fun_=\n";
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        int i = 1, n = 0, m = 0, h = 0;
        while(a.lex[i] >= '0' && a.lex[i] <= '9') {
            n *= 10;
            n += a.lex[i] - '0';
            i++;
        }
        i++;
        while(a.lex[i] >= '0' && a.lex[i] <= '9') {
            m *= 10;
            m += a.lex[i] - '0';
            i++;
        }
        i++;
        while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
            h *= 10;
            h += a.lex[i] - '0';
            i++;
        }
        obl_vid[n][m][h].znach = its(f2);
        auto x = a;
        x.lex = its(f2);
        x.num = 7;
        pol.push(x);
        //cout << pol.top().lex << "\n";
    } else if(s == ">>") {
        b = pol.top();
        pol.pop();
        //if(b.num == 2) {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            //cout << n << " " << m << " " << h << " AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA\n";
            cin >> obl_vid[n][m][h].znach;
        //}
    } else if(s == "<<") {
        b = pol.top();
        pol.pop();
        if(b.num == 2) {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            cout << obl_vid[n][m][h].znach /*<< /*" etot vivod chtoby ti zaplakala\n"*/;
        } else if(b.num == 7 || b.num == 1) {
            //cout << "incinout\n";
            cout << b.lex /*<< /*" cout\n"*/;
        }
    } else if(s == "%"){
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        int f1, f2;
        if(a.num == 7) {
            f1 = sti(a.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                n *= 10;
                n += a.lex[i] - '0';
                i++;
            }
            i++;
            while(a.lex[i] >= '0' && a.lex[i] <= '9') {
                m *= 10;
                m += a.lex[i] - '0';
                i++;
            }
            i++;
            while(i < a.lex.size() && a.lex[i] >= '0' && a.lex[i] <= '9') {
                h *= 10;
                h += a.lex[i] - '0';
                i++;
            }
            f1 = sti(obl_vid[n][m][h].znach);
        }
        if(b.num == 7) {
            f2 = sti(b.lex);
        } else {
            int i = 1, n = 0, m = 0, h = 0;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                n *= 10;
                n += b.lex[i] - '0';
                i++;
            }
            i++;
            while(b.lex[i] >= '0' && b.lex[i] <= '9') {
                m *= 10;
                m += b.lex[i] - '0';
                i++;
            }
            i++;
            while(i < b.lex.size() && b.lex[i] >= '0' && b.lex[i] <= '9') {
                h *= 10;
                h += b.lex[i] - '0';
                i++;
            }
            f2 = sti(obl_vid[n][m][h].znach);
        }
        auto x = a;
        x.lex = its(f1 % f2);
        x.num = 7;
        pol.push(x);
    } /*else if(s == "&&") {
        b = pol.top();
        pol.pop();
        a = pol.top();
        pol.pop();
        if(a.lex == "true" && b.lex == "true") {
            pol.push(a);
        } else {
            a.lex = "false";
            pol.push(a);
        }
    }/*else if(s == "!") {
        b = pol.top();
        pol.pop();
        if(b.lex == "true") {
            b.lex = "false";
        } else {
            b.lex = "true";
        }
        pol.push(b);
    }*/
}

int per(string s) { ///переход
    if(s[0] == 'p') {
        if(pol.top().lex == "false") {
            return sti(s.substr(1, s.size() - 1));
        } else {
            return -1;
        }
    } else {
        return sti(s.substr(1, s.size() - 1));
    }
}

void intepreter() {
    for(int i = beg; i < ind; i++) {
        //cout << i << " " << com[i].lex << " " << com[i].num << " intep_i\n";
        if(com[i].num == 3) {
            fun(com[i].lex);
            //cout << pol.top().lex << " intep_afterop\n";
        } else if(com[i].num == 8) {
            int j = per(com[i].lex) - 1;
            if(j >= 0) {
                i = j;
            }
        } else {
            pol.push(com[i]);
        }
    }
}
int main() {
    FILE *fp = fopen("program.txt", "r");
    FILE *fp3 = fopen("need.txt", "w+");
    FILE *fp1 = fopen("leksems.txt", "w");
    FILE *fp2 = fopen("antispam.txt", "w");
    char last, cur;
    string lex;
    vector<string> res; //зарезервированные слова
    res.push_back("#include");
    res.push_back("#define");
    res.push_back("bool");
    res.push_back("break");
    res.push_back("char");
    res.push_back("continue");
    res.push_back("double");
    res.push_back("else");
    res.push_back("float");
    res.push_back("for");
    res.push_back("if");
    res.push_back("int");
    res.push_back("long");
    res.push_back("namespace");
    res.push_back("return");
    res.push_back("unsigned");
    res.push_back("using");
    res.push_back("void");
    res.push_back("while");
    res.push_back("true");
    res.push_back("false");
    res.push_back("to");
    res.push_back("downto");
    res.push_back("cinout");
    res.push_back("do");
    /// спасибо Оля
    char a, b;
    fscanf(fp, "%c", &b);
    a = b;
    while(!feof(fp)){
        b = a;
        fscanf(fp, "%c", &a);
        if(b == '/' && a == '/'){
            while(!feof(fp) && a != '\n'){
                b = a;
                fscanf(fp, "%c", &a);
            }
            b = a;
            fscanf(fp, "%c", &a);
            continue;
        }
        else{
            if(b == '/' && a == '*'){
                while(!(b=='*' && a=='/')){
                    b = a;
                    fscanf(fp, "%c", &a);
                }
                b = a;
                fscanf(fp, "%c", &a);
                continue;
            }
            else
                fprintf(fp3, "%c", b);
        }
    }
    fprintf(fp3, "%c", a); /// спасибо Оля
    fseek(fp, 0, SEEK_SET);
    fseek(fp3, 0, SEEK_SET);
    int h = 0; //переменная отслеживающая состояние
    fscanf(fp3, "%c", &cur);
    int line = 1;
    while(!feof(fp3)) {
        cout << last << " \n";
        if(h == 2) {
            /// спасибо Оля
            if(last == '=') {
                lex += last;
                if(cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == ';' || last == '.' || last == ',' || last == ':' || last == '?' || last == '{' || last == '}'){
                lex += last;
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 4 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '%'){
                lex += last;
                if(cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '+'){
                lex += last;
                if(cur == '+' || cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '-'){
                lex += last;
                if(cur == '-' || cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '*'){
                lex += last;
                if(cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '/'){
                lex += last;
                if(cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '!'){
                lex += last;
                if(cur == '='){
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '(' || last == ')' || last == '[' || last == ']'){
                lex += last;
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 5 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '<') {
                lex += last;
                if(cur == '<' || cur == '=') {
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '>') {
                lex += last;
                if(cur == '>' || cur == '=') {
                    lex += cur;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 3 %d\n", line);
                lex.clear();
                h = 0;
                continue;
            }
            if(last == '"' || last == '\'') {
                fprintf(fp1, "%c", last);
                fprintf(fp2, "%c", last);
                fprintf(fp1, " 3 %d\n", line);
                bool f = 1;
                if(last == '"') {
                    f = 0;
                }
                last = cur;
                fscanf(fp3, "%c", &cur);
                while(!f && last != '"' && last != 10 || f && last != '\'' && last != 10) {
                    lex += last;
                    last = cur;
                    fscanf(fp3, "%c", &cur);
                }
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 7 %d\n", line);
                lex.clear();
                fprintf(fp1, "%c", last);
                fprintf(fp2, "%c", last);
                fprintf(fp1, " 3 %d\n", line);
                h = 0;
                continue;
            }
            if(last == ' ' || last == '\n') {
                h = 0;
                continue;
            }
            h = 3;
            continue;
        } /// спасибо Оля
        if(cur == '\n') {
            line++;
        }
        last = cur;
        fscanf(fp3, "%c", &cur);
        if(h == 0) {
            if(last >= 'A' && last <= 'Z' || last >= 'a' && last <= 'z' || last == '#') {
                lex += last;
                h = 1;
                continue;
            }
            if(last >= '0' && last <= '9') {
                lex += last;
                continue;
            } else if(last == '!' || last == '=' || last == '+' || last == '-' ||
                      last == ';' || last == '.' || last == ',' || last == ':' ||
                      last == '?' || last == '{' || last == '}' || last == '*' ||
                      last == '/' || last == '(' || last == ')' || last == '[' ||
                      last == ']' || last == '"' || last == '\'' || last == '<' ||
                      last == '>' || last == ' ' || last == '\n' || last == '%') {
                if(lex.size()) {
                    for(int i = 0; i < lex.size(); i++) {
                        fprintf(fp1, "%c", lex[i]);
                        fprintf(fp2, "%c", lex[i]);
                    }
                    fprintf(fp1, " 7 %d\n", line);
                }
                h = 2;
                lex.clear();
                continue;
            } else {
                lex += last;
                h = 3;
                continue;
            }
        }
        if(h == 1) {
            if(last >= 'A' && last <= 'Z' || last >= 'a' && last <= 'z' || last >= '0' && last <= '9') {
                lex += last;
                continue;
            } else if(last == '!' || last == '=' || last == '+' || last == '-' ||
                      last == ';' || last == '.' || last == ',' || last == ':' ||
                      last == '?' || last == '{' || last == '}' || last == '*' ||
                      last == '/' || last == '(' || last == ')' || last == '[' ||
                      last == ']' || last == '"' || last == '\'' || last == '<' ||
                      last == '>' || last == ' ' || last == '\n'){
                for(int i = 0; i < res.size(); i++) {
                    if(lex == res[i]) {
                        for(int j = 0; j < lex.size(); j++) {
                            fprintf(fp1, "%c", lex[j]);
                            fprintf(fp2, "%c", lex[j]);
                        }
                        fprintf(fp1, " 1 %d\n", line);
                        h = 2;
                        lex.clear();
                        break;
                    }
                }
                if(h == 2) {
                    continue;
                } else {
                    for(int i = 0; i < lex.size(); i++) {
                        fprintf(fp1, "%c", lex[i]);
                        fprintf(fp2, "%c", lex[i]);
                    }
                    fprintf(fp1, " 2 %d\n", line);
                    h = 2;
                    lex.clear();
                    continue;
                }
            } else {
                lex += last;
                h = 3;
                continue;
            }
        }
        if(h == 3) {
            if(last != ' ' && last != '\n') {
                lex += last;
                continue;
            } else {
                for(int i = 0; i < lex.size(); i++) {
                    fprintf(fp1, "%c", lex[i]);
                    fprintf(fp2, "%c", lex[i]);
                }
                fprintf(fp1, " 6 %d\n", line);
                h = 0;
                lex.clear();
                continue;
            }
        }
    }
    fclose(fp);
    fclose(fp1);
    fclose(fp2);
    fclose(fp3);
    try {
        S();
    }
    catch(string s) {
        //cout << " ENNDDDDD\n";
        cout << "\n\n" << s << " in line " << linec;
        return 0;
    }
    cout << "\n\n\nOK\n";
    intepreter();
}
