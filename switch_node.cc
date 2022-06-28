#include<iostream>
#include<fstream>
#include<string>
#include<sstream>
#include<algorithm>
#include<vector>
#include<map>
#include<set>
#include"lib.h"
#include<queue>
using namespace std;
#define MAX 100
#define inf 65535
enum{
	black=0,white=1
};

enum{
	ptp=0,stb=1
};


struct rt_lsa{
	string adv;
	vector<struct link> link_info;
    rt_lsa():adv(""){};
};

struct link{
	int type;/*link type*/
	int cost;
	string link_id,link_data;
    link():type(ptp),cost(0),link_id(""),link_data(""){};
};

struct node{
	string rt_id;
	int distance;
	int color;
	struct node *pre;/*pre node*/
	struct node *backup; /*backup node */
	vector<struct node *> children; /*children node*/
	node():rt_id(""),distance(inf),color(white),pre(NULL),backup(NULL){};
};/*node info*/

vector<struct node *> nodebase;/*node base*/
vector<struct rt_lsa *> database;/*lsa base*/
set<string> network; /*network segment*/
map<string,struct node *> mp;/*map from ip to node pointer*/
map<string,struct rt_lsa *> rt; /*map from ip to data pointer*/
map<string,string> bkroute; /*backup route table*/
map<string,string> bkroute_node; /*backup route table(single node failure)*/
map<string,string> route; /*main route table*/
string host; /*host which runs the algorithm*/

void initial();/*generate node*/
void init_value(); /*set node value init state*/
void dijk_pq(struct node *);
void get_rt_lsa();
void get_host();
void dump_database();
void dump_nodebase();
void dump_distance();
void dump_black_node();
void dump_bkroute();
void dump_bkroute_node();
int comp_ip(string &,string &,string &);
int cnt(struct node *,int);
string find_gateway(struct node *); /*find the gateway*/
vector<string> find_interface(struct node *); /*find self interface ip addr*/
void dfs(struct node *); /*dfs to find each node's backup nexthop*/
void dfs_node(struct node *); /*dfs to find each node's backup nexthop(single node failure)*/
void mark(struct node *,int); /*mark sub tree color*/
void make_bknext_hop(); /*calculate backup next hop*/
void make_bknext_hop_node(); /*calculate backup next hop(single node failure)*/
void get_main_route();

int main(){
	get_rt_lsa(); /*get router lsa*/

	initial(); /*init*/

	get_host(); /*get host id*/

    get_main_route(); /*get main route table*/

	make_bknext_hop(); /*get backup route table*/

    dump_bkroute(); /*dump backup route*/

    make_bknext_hop_node(); /*get backup route table(single node failure)*/

    dump_bkroute_node(); /*dump backup route(single node failure)*/

    /*dijk_pq(mp["1.1.1.7"]);

    dfs_node(mp["1.1.1.7"]);

    for(int i = 0;i < nodebase.size();i++)
        if(nodebase[i] -> backup)
            cout<<nodebase[i] -> rt_id<<" "<<nodebase[i] -> backup -> rt_id<<endl;

    dfs(mp["1.1.1.24"]);

    cout<<mp[host] -> pre -> rt_id<<endl;

    for(int i = 0;i < nodebase.size();i++){
        cout<<"self:"<<nodebase[i] -> rt_id<<endl;
        if(nodebase[i] -> pre)
            cout<<"parent:"<<nodebase[i] -> pre -> rt_id<<endl;
        for(int j = 0;j < nodebase[i] -> children.size();j++)
            cout<<"children:"<<(nodebase[i] -> children)[j] -> rt_id<<endl;
        cout<<endl<<endl;
    }
    dump_distance();*/
}

void initial(){
	struct node *nd;
	int i;
	for(i = 0;i < database.size();i++){
		nd=new node();
		nd -> rt_id = database[i] -> adv;
		nodebase.push_back(nd);
		mp[nd->rt_id] = nd;
	}
}

void get_rt_lsa(){
	ifstream in("rtlsa.txt");
	string s1,s2;
	struct rt_lsa *p;
	while(in.peek() != EOF){
		getline(in,s1);
		if(s1[0] != 'a'){
			getline(in,s2);
			struct link t;
			t.cost = 1;
            if(s2.substr(0,3) == "255")
                t.type= stb;
            else
			    t.type = ptp;
			t.link_id = s1;
			t.link_data = s2;
			(p->link_info).push_back(t);
		}
		else{	
			string sub = s1.substr(4,s1.size()-4);
			p = new rt_lsa();
			p->adv = sub;
			database.push_back(p);
			rt[sub] = p;
		}
	}
    in.close();
}

void get_host(){
	ifstream in("host.txt");
	string s;
	while(in.peek() != EOF){
		getline(in,s);
		host = s;
	}
    in.close();
}

void dump_database(){
	cout<<database.size()<<endl;
	for(int i = 0;i < database.size();i++){
		cout << database[i] -> adv << endl;
		for(int j = 0;j < (database[i] -> link_info).size();j++)
			cout<<(database[i]->link_info)[j].link_id<<(database[i]->link_info)[j].link_data<<endl;
	}
}


void dump_nodebase(){
	for(int i = 0;i < nodebase.size();i++)
		cout<<nodebase[i]->rt_id<<endl;
}

void dump_distance(){
    for(int i = 0; i < nodebase.size();i++)
        cout<<nodebase[i] -> rt_id<<":"<<nodebase[i] -> distance<<endl;
}

void dump_black_node(){
	for(int i = 0;i < nodebase.size();i++)
		if(nodebase[i] -> color == black)
			cout<<nodebase[i] -> rt_id <<endl;
}


void init_value(){
	for(int i = 0;i < nodebase.size();i++){
		nodebase[i] -> distance = inf;
		nodebase[i] -> color = white;
		nodebase[i] -> pre = NULL;
		nodebase[i] -> children.clear();
		nodebase[i] -> backup = NULL;
	}
}


void dijk_pq(struct node *root){
	int n = nodebase.size();
	init_value();
	priority_queue<pair<int,string>,vector<pair<int,string> >,greater<pair<int,string> > > pq;
	map<string,int> vis;
	map<string,int> dis;
	map<string,string> prev;
	map<string,vector<string> > children;
	for(int i = 0;i < database.size();i++)
		dis[database[i] -> adv] = inf;
	pair<int,string> t(0,root -> rt_id);
	pq.push(t);
	dis[root -> rt_id] = 0;
	prev[root -> rt_id] = "";
	while(!pq.empty()){
		pair<int,string> top = pq.top();
		pq.pop();
		if(!vis[top.second]){
			vis[top.second] = 1;
			for(int i = 0;i	< rt[top.second]->link_info.size();i++)
				if((rt[top.second] -> link_info)[i].type == ptp&&!vis[(rt[top.second] -> link_info)[i].link_id])
					if(dis[(rt[top.second] -> link_info)[i].link_id] > top.first+(rt[top.second] -> link_info)[i].cost || (dis[(rt[top.second] -> link_info)[i].link_id] == top.first+(rt[top.second] -> link_info)[i].cost && comp_ip((rt[top.second] -> link_info)[i].link_id,top.second,prev[(rt[top.second] -> link_info)[i].link_id]))){
						dis[(rt[top.second] -> link_info)[i].link_id] = top.first+(rt[top.second] -> link_info)[i].cost;
						if(prev[(rt[top.second] -> link_info)[i].link_id] != top.second){
							children[top.second].push_back((rt[top.second] -> link_info)[i].link_id);
							vector<string>::iterator pos;
pos = find(children[prev[(rt[top.second] -> link_info)[i].link_id]].begin(),children[prev[(rt[top.second] -> link_info)[i].link_id]].end(),(rt[top.second] -> link_info)[i].link_id);
                            if(pos != children[prev[(rt[top.second] -> link_info)[i].link_id]].end())
							    children[prev[(rt[top.second] -> link_info)[i].link_id]].erase(pos);
							prev[(rt[top.second] -> link_info)[i].link_id] = top.second;
						}
						pair<int,string> nb(dis[(rt[top.second] -> link_info)[i].link_id],(rt[top.second] -> link_info)[i].link_id);
						pq.push(nb);
					}
		}
	}
	root -> pre = NULL;
	root -> distance = 0;
	for(int j = 0;j < children[root -> rt_id].size();j++)
		(root -> children).push_back(mp[children[root -> rt_id][j]]);
	for(int i = 0;i < n ;i++)
		if(nodebase[i] -> rt_id != root -> rt_id){
			nodebase[i] -> pre = mp[prev[nodebase[i] -> rt_id]];
			nodebase[i] -> distance = dis[nodebase[i] -> rt_id];
			for(int j = 0;j < children[nodebase[i] -> rt_id].size();j++)
				(nodebase[i] -> children).push_back(mp[children[nodebase[i] -> rt_id][j]]);
		}
}

void make_bknext_hop(){
	int i,j;
	for(i = 0;i < nodebase.size();i++){
		dijk_pq(nodebase[i]); /*create spf tree with root nodebase[i]*/
		dfs(nodebase[i]); /*dfs spf tree to find each node's backup next hop*/
        if(mp[host] -> backup != NULL){
            string gateway = find_gateway(mp[host] -> backup);
            vector<string> net = find_interface(nodebase[i]);
            for(j = 0;j < net.size();j++){
                if(route[net[j]] != gateway && bkroute[net[j]] == "")
                    bkroute[net[j]] = gateway;
                network.insert(net[j]);
            }
        }
	}
}

void dfs(struct node *root){
	if(!root)
		return;
	if(root -> backup == NULL){
	    mark(root,black);
	    int flag = 0;
	    queue<struct node *> q;
	    q.push(root);
	    struct node *top = NULL;
	    while(!q.empty()){
            int len = q.size();
            for(int j = 0 ;j < len;j++){
		        top = q.front();
		        q.pop();
                for(int k = 0;k < top -> children.size();k++)
                    q.push((top -> children)[k]);
		        for(int i = 0;i < (rt[top -> rt_id] -> link_info).size();i++)
			        if((rt[top -> rt_id] ->link_info)[i].type == ptp && mp[(rt[top -> rt_id] ->link_info)[i].link_id] -> color == white && (rt[top -> rt_id] ->link_info)[i].link_id != root ->pre -> rt_id ){
				        top -> backup = mp[(rt[top -> rt_id] ->link_info)[i].link_id];
				        flag = 1; 
				        break;
			        }
                if(flag)
                    break;
            }
            if(flag)
                break;
        }
        if(flag){
	        while(top != root){
		        if(!top -> pre -> backup)
			        top -> pre -> backup = top;
		        top = top -> pre;
	        }
        }
	    mark(root,white);
    }
    for(int i = 0;i < root -> children.size();i++)
        dfs((root -> children)[i]);
}

void mark(struct node *root,int color){
	if(!root)
		return;
	root -> color = color;
	for(int i =0; i < root -> children.size();i++)
		mark((root -> children)[i],color);
}

string find_gateway(struct node *nbr){
    for(int i = 0;i < (rt[nbr -> rt_id] -> link_info).size();i++)
        if((rt[nbr -> rt_id] -> link_info)[i].type == ptp && (rt[nbr -> rt_id] -> link_info)[i].link_id == host)
            return (rt[nbr -> rt_id] -> link_info)[i].link_data;
    return "";
}

vector<string> find_interface(struct node *root){
    vector<string> ans;
    for(int i = 0;i < (rt[root -> rt_id] -> link_info).size();i++)
        if((rt[root -> rt_id] -> link_info)[i].type == stb)
            ans.push_back((rt[root -> rt_id] -> link_info)[i].link_id+"/24");
    return ans;
}

void dump_bkroute(){
    set<string> ::iterator it;
    ofstream out("bkroute.txt");
    for(it = network.begin();it != network.end();it++)
		out<<*it<<"\t"<<bkroute[*it]<<endl;
	out.close();
}

void get_main_route(){
    ifstream in("nowtable");
    string s,net,via,gate;
    while(in.peek() != EOF){
        getline(in,s);
        stringstream ss(s);
        ss>>net>>via>>gate;
        route[net] = gate;
    }
    in.close();
}

int comp_ip(string &self,string &top,string &pre){
    string top_ip,pre_ip;
    for(int i = 0;i < (rt[self] -> link_info).size();i++){
        if((rt[self] -> link_info)[i].type == ptp && (rt[self] -> link_info)[i].link_id == top)
            top_ip = (rt[self] -> link_info)[i].link_data;
        if((rt[self] -> link_info)[i].type == ptp && (rt[self] -> link_info)[i].link_id == pre)
            pre_ip = (rt[self] -> link_info)[i].link_data;
    }
    stringstream ss1(top_ip),ss2(pre_ip);
    vector<string> sub1,sub2;
    string t;
    while(getline(ss1,t,'.'))
        sub1.push_back(t);
    while(getline(ss2,t,'.'))
        sub2.push_back(t);
    if(stoi(sub1[2]) < stoi(sub2[2]))
        return 1;
    return 0;
}

//single node failure
void dfs_node(struct node *root){ 
	if(!root)
		return;
    if(root -> pre){
	    mark(root,black);
        for(int i = 0;i < root -> children.size();i++)
            if((root -> children)[i] -> backup)
                mark((root->children)[i],white);
        while(cnt(root,black) > 1){
	        int flag = 0;
	        queue<struct node *> q;
            for(int k = 0;k < root -> children.size();k++)
                if((root -> children)[k] -> color == black){
                    q.push((root -> children)[k]);
					break;
				}
	        struct node *top = NULL,*child = NULL;
	        while(!q.empty()){
                int len = q.size();
                for(int j = 0 ;j < len;j++){
		            top = q.front();
		            q.pop();
                    for(int k = 0;k < top -> children.size();k++)
                        if((top -> children)[k] -> color == black)
                            q.push((top -> children)[k]);
		            for(int i = 0;i < (rt[top -> rt_id] -> link_info).size();i++)
			            if((rt[top -> rt_id] ->link_info)[i].type == ptp && mp[(rt[top -> rt_id] ->link_info)[i].link_id] -> color == white){
                            top -> backup = mp[(rt[top -> rt_id] ->link_info)[i].link_id];
				            flag = 1;
				            break;
			            }
                    if(flag)
                        break;
                }
                if(flag)
                    break;
            }
            if(flag){
	            while(top != root){
		            if(!top -> pre -> backup)
			            top -> pre -> backup = top;
                    child = top;
		            top = top -> pre;
	            }
            }
	        mark(child,white);
        }
        mark(root,white);
    }
    for(int i = 0;i < root -> children.size();i++)
        dfs_node((root -> children)[i]);
}

int cnt(struct node *root,int color){
    if(!root)
        return 0;
    int ans = 0;
    if(root -> color == color)
        ans++;
    for(int i = 0;i < (root -> children).size();i++)
        ans+=cnt((root -> children)[i],color);
    return ans;
}


void make_bknext_hop_node(){
	int i,j;
	for(i = 0;i < nodebase.size();i++){
		dijk_pq(nodebase[i]); /*create spf tree with root nodebase[i]*/
		dfs_node(nodebase[i]); /*dfs spf tree to find each node's backup next hop*/
        if(mp[host] -> backup != NULL){
            string gateway = find_gateway(mp[host] -> backup);
            vector<string> net = find_interface(nodebase[i]);
            for(j = 0;j < net.size();j++){
                if(route[net[j]] != gateway && bkroute_node[net[j]] == "")
                    bkroute_node[net[j]] = gateway;
                network.insert(net[j]);
            }
        }
	}
}


void dump_bkroute_node(){
    set<string> ::iterator it;
    ofstream out("bkroutenode.txt");
    for(it = network.begin();it != network.end();it++)
		out<<*it<<"\t"<<bkroute_node[*it]<<endl;
	out.close();
}
