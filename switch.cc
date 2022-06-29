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
#define M 4
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
    vector<struct node *> children; /*children node*/
	node():rt_id(""),distance(inf),color(white),pre(NULL){};
};/*node info*/

vector<struct node *> nodebase;/*node base*/
vector<struct rt_lsa *> database;/*lsa base*/
map<string,struct node *> mp;/*map from ip to node pointer*/
map<string,struct rt_lsa *> rt; /*map from ip to data pointer*/
set<pair<string,string> > st; /*edge set*/
map<pair<string,string>,pair<string,set<string> > > bkroute_addr; /*bknext_hop hash set,from which we can fetch the next hop*/
map<string,vector<pair<string,set<string> > > > bkroute_addr_node; /*bknext_hop hash set,from which we can fetch the next hop(single node failure)*/
map<pair<string,string>,set<string> > treenet; /*tree's network segment*/
map<pair<string,string>,string> subtree; /*in which sub tree?*/


struct node *out=NULL,*op=NULL;
struct node *bknext_hop=NULL;
set<string> network;
string local,nbr; /*two nodes between which the link failed*/
string host; /*host which runs the algorithm*/
string gateway; /*bknext_hop's interface addr which connects host*/
string local_ip,nbr_ip; /*ip that connect two nodes which the link failed*/
set<string> selfnet;

void initial();/*generate node*/
void init_value(); /*set node value init state*/
int comp_ip(string &,string &,string &);/*compare ip*/
void dijk(struct node *);/*paint node black*/
void dijk_pq(struct node *);
void dijk_pq2(struct node *);
void backtrace(struct node *);
struct node *loop();/*loop to find the nearest exit to white node j,node i*/
void get_rt_lsa();
void get_host();
void get_local();
void get_nbr();
void dump_database();
void dump_nodebase();
void dump_distance();
void dump_black_node();
void dump_out_node();
void find_bknext_hop();
void find_gateway();
void find_interface_addr();
void dump_reverse_color_node_if(set<string> &);
void dump_bkroute_node();
void handle_all_down_link();
void handle_all_down_link2();
void handle_all_node();
void make_net(set<string> &,struct node *);
void mark(struct node *,int);
void make_dfs_list(struct node *,vector<struct node *> &);
struct node *seq(struct node *,struct node *,struct node *);




int main(){
	get_rt_lsa(); /*get router lsa*/

	initial(); /*init*/

	get_host(); /*get host id*/

	handle_all_down_link2();/*get backup nexthop*/

    handle_all_node();

    dump_bkroute_node();

    /*dijk_pq2(mp["1.1.1.2"]);
    
    for(int i = 0;i < nodebase.size();i++){
        cout<<"self:"<<nodebase[i] -> rt_id<<endl;
        if(nodebase[i] -> pre)
            cout<<"parent:"<<nodebase[i] -> pre -> rt_id<<endl;
        for(int j = 0;j < nodebase[i] -> children.size();j++)
            cout<<"children:"<<(nodebase[i] -> children)[j] -> rt_id<<endl;
        cout<<endl<<endl;
    }
    mark(mp["1.1.1.1"],black);
    dump_black_node();
    cout<<endl;
    mark(mp["1.1.1.1"],white);
    mark(mp["1.1.1.3"],black);
    dump_black_node();
    dump_distance();*/
}

void initial(){
	struct node *nd;
	int i;
	for(i = 0;i < database.size();i++){
		nd = new node();
		nd -> rt_id = database[i] -> adv;
		nodebase.push_back(nd);
		mp[nd->rt_id] = nd;
	}
}


/*detach the black sub tree*/
void dijk(struct node *root){
	if(!root)
		return;
	init_value();
	int i,j,cnt = nodebase.size()-1;
	map<struct node *,int> vis;/*visit map*/
	vector<struct node *> s;/*found shortest path set*/
	struct node *t;
	vis[root] = 1;
	s.push_back(root);
	root -> distance = 0;
	root -> pre = NULL;
	while(cnt){
		int n = s.size(),dis = inf;
		cnt--;
		for(i = 0;i < database.size();i++)
			if(!vis[mp[database[i] -> adv]])
				for(j = 0;j < (database[i] -> link_info).size();j++)
					if((database[i]->link_info)[j].link_id == s[n-1] -> rt_id)
						if(mp[database[i] -> adv] -> distance > (database[i] -> link_info)[j].cost + s[n-1] -> distance){
							mp[database[i] -> adv] -> distance = (database[i] -> link_info)[j].cost + s[n-1] -> distance;
							mp[database[i] -> adv] -> pre = s[n-1];
						}
		for(i = 0;i < nodebase.size();i++)
			if(!vis[nodebase[i]] && dis > nodebase[i] -> distance){
				dis = nodebase[i] -> distance;
				t = nodebase[i];
			}
		vis[t] = 1;
		s.push_back(t);
	}
	for(i = 0;i < s.size();i++)
		backtrace(s[i]);
}

/*backtrace to the root node so as to determine whether or not paint the node*/
void backtrace(struct node *root){
	struct node *p = root;
	int flag = 0;
    if(root == mp[local]){
        root -> color = black;
        return;
    }
	while(p -> pre){
		if(p -> pre == mp[local]){
			flag = 1;
			break;
		}
		p = p -> pre;
	}
	if(flag)
		root -> color = black;
}

struct node *loop(){
	queue<struct node *> q;
    int dis = 65535;
    struct node *ans = NULL;
	for(int i = 0;i < nodebase.size();i++)
		if(nodebase[i] -> color == black)
			q.push(nodebase[i]);
	while(!q.empty()){
		int len = q.size();
		for(int i = 0;i < len;i++){
			struct node *top = q.front();
			q.pop();
			for(int j = 0;j < database.size();j++)
				if(mp[database[j] -> adv] -> color == white && (database[j] -> adv != nbr||top != mp[local]))
					for(int k = 0;k < (database[j] -> link_info).size();k++)
						if((database[j] -> link_info)[k].link_id == top->rt_id)
                            if(dis > top -> distance + mp[database[j] -> adv] -> distance){
                                dis = top -> distance + mp[database[j] -> adv] -> distance;
							    op = mp[database[j] -> adv];
							    ans = top;
                            }
		}
	}
	return ans;
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
                t.type = stb;
            else
			    t.type = ptp;
			t.link_id = s1;
			t.link_data = s2;
			(p -> link_info).push_back(t);
            if(t.type == ptp){
                if(t.link_id < p -> adv){
                    pair<string,string> pr(t.link_id,p -> adv);
                    st.insert(pr);
                }
                else{
                    pair<string,string> pr(p -> adv,t.link_id);
                    st.insert(pr);
                }
            }
		}
		else{	
			string sub = s1.substr(4,s1.size()-4);
			p = new rt_lsa();
			p -> adv = sub;
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
    for(int i = 0;i < (rt[host] -> link_info).size();i++)
        if((rt[host] -> link_info)[i].type == stb)
            selfnet.insert((rt[host] -> link_info)[i].link_id);
}


void get_local(){
    ifstream in("localid.txt");
    getline(in,local);
    in.close();
}

void get_nbr(){
    ifstream in("nbrid.txt");
    getline(in,nbr);
    in.close();
}


void dump_database(){
	cout<<database.size()<<endl;
	for(int i = 0;i < database.size();i++){
		cout << database[i] -> adv << endl;
		for(int j = 0;j < (database[i] -> link_info).size();j++)
			cout<<(database[i] -> link_info)[j].link_id<<(database[i] -> link_info)[j].link_data<<endl;
	}
}


void dump_nodebase(){
	for(int i = 0;i < nodebase.size();i++)
		cout<<nodebase[i]->rt_id<<endl;
}

void dump_black_node(){
	for(int i = 0;i < nodebase.size();i++)
		if(nodebase[i] -> color == black)
			cout<<nodebase[i] -> rt_id <<endl;
}

void dump_distance(){
	for(int i = 0;i < nodebase.size();i++)
	    cout<<nodebase[i] -> rt_id<<":"<<nodebase[i] -> distance <<endl;
}

void dump_out_node(){
    cout<<"exit node id:"<<out -> rt_id<<endl;
    cout<<"exit node's nbr:"<<op -> rt_id<<endl;
}

void find_bknext_hop(){
	struct node *p;
	if(mp[host] == NULL)
		return;
	if (out == mp[host]){
		bknext_hop = op;
		return;
	}
	if(op == mp[host]){
		bknext_hop = out;
		return;
	}
	switch(mp[host] -> color){
		case black:
			p = out;
			while(p -> pre){
				if(p -> pre == mp[host]){
					bknext_hop = p;
					break;
				}
				p = p->pre;
			}
		;break;
		case white:
			p = op;
			while(p -> pre){
				if(p -> pre == mp[host]){
					bknext_hop = p;
					break;
				}
				p = p -> pre;
			}
		
		;break;
		default:;break;
	}
}

void dump_reverse_color_node_if(set<string> &ans){
	if(mp[host] == NULL)
		return;
    int color = mp[host] -> color;
    for(int j = 0;j<database.size();j++)
        if(mp[database[j] -> adv] -> color == !color)
            for(int i =0;i<(database[j]->link_info).size();i++)
                if((database[j] -> link_info)[i].type == stb && selfnet.find((database[j] -> link_info)[i].link_id) == selfnet.end())
					ans.insert((database[j] -> link_info)[i].link_id+"/24");
}

void find_gateway(){
	int i,j;
	if(bknext_hop == NULL)
		return;
	if(database.size() == 0)
		return;
	for(i = 0;i < database.size();i++)
		if(database[i] -> adv == bknext_hop -> rt_id)
			break;
	for(j = 0;j < (database[i] -> link_info).size();j++)
		if((database[i] -> link_info)[j].link_id == host)
			break;
    if(j < (database[i] -> link_info).size())
	    gateway = (database[i] -> link_info)[j].link_data;
}

void find_interface_addr(){
	int i,j;
	for(i = 0; i < database.size();i++)
		if(database[i] -> adv == local){
			for(j = 0 ;j < (database[i] -> link_info).size();j++)
				if((database[i] -> link_info)[j].link_id == nbr){
					local_ip=(database[i] -> link_info)[j].link_data;
					break;
				}
		}
		else if(database[i] -> adv == nbr){
			for(j = 0;j < (database[i] -> link_info).size();j++)
				if((database[i] -> link_info)[j].link_id == local){
					nbr_ip=(database[i] -> link_info)[j].link_data;
					break;
				}
		}
}

void init_value(){
	for(int i = 0;i < nodebase.size();i++){
		nodebase[i] -> distance = inf;
		nodebase[i] -> color = white;
		nodebase[i] -> pre = NULL;
        (nodebase[i] -> children).clear();
	}
}

void handle_all_down_link(){
	int i,j,k,n;
	for(i = 0;i < database.size() ;i++)
		for(j = i+1;j < database.size();j++)
			for(k = 0;k < (database[i] -> link_info).size();k++)
				if((database[i] -> link_info)[k].link_id == database[j] -> adv){
					if(database[i] -> adv < database[j] -> adv){
						local = database[i] -> adv;
						nbr = database[j] -> adv;
					}
					else{
						local = database[j] -> adv;
						nbr = database[i] -> adv;
					}
					pair<string,string> t(local,nbr);
					dijk(mp[nbr]);
                    out = NULL;
					out = loop();
					bknext_hop=NULL;
                    if(out != NULL){
					    find_bknext_hop();
						if(bknext_hop != NULL){
							find_interface_addr();
							find_gateway();
							bkroute_addr[t].first=gateway;
							dump_reverse_color_node_if(bkroute_addr[t].second);
						}
                    }
				}
}

void dijk_pq(struct node *root){
	int n = nodebase.size();
	init_value();
	priority_queue<pair<int,string>,vector<pair<int,string> >,greater<pair<int,string> > > pq;
	map<string,int> vis;
	map<string,int> dis;
	map<string,string> prev;
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
						prev[(rt[top.second] -> link_info)[i].link_id] = top.second;
						pair<int,string> nb(dis[(rt[top.second] -> link_info)[i].link_id],(rt[top.second] -> link_info)[i].link_id);
						pq.push(nb);
					}
		}
	}
	root -> pre = NULL;
	root -> distance = 0;
	for(int i = 0;i < n ;i++)
		if(nodebase[i] -> rt_id != root -> rt_id){
			nodebase[i] -> pre = mp[prev[nodebase[i] -> rt_id]];
			nodebase[i] -> distance = dis[nodebase[i] -> rt_id];
		}
	for(int i = 0;i < nodebase.size();i++)
		backtrace(nodebase[i]);
}


void handle_all_down_link2(){
    set<pair<string,string> >::iterator beg;
    set<string>::iterator it;
    string filename;
    for(beg = st.begin();beg != st.end();beg++){
        local =(*beg).first;
        nbr = (*beg).second;
        pair<string,string> t(local,nbr);
        dijk_pq(mp[nbr]);
        out = NULL;
        out = loop();
        bknext_hop=NULL;
        if(out != NULL){
	        find_bknext_hop();
		    if(bknext_hop != NULL){
			    find_interface_addr();
				find_gateway();
				bkroute_addr[t].first=gateway;
				dump_reverse_color_node_if(bkroute_addr[t].second);
                filename=local+nbr;
                ofstream out(filename.c_str());
                for(it=bkroute_addr[t].second.begin();it!=bkroute_addr[t].second.end();it++)
                    out<<gateway<<"\t"<<*it<<endl;
                out.close();
			}
        }
    }                                                      
}

//single node failure
void dijk_pq2(struct node *root){
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

struct node *seq(struct node *root1,struct node *root2,struct node *root){
    int dis = inf;
    struct node *ans = NULL;
    vector<struct node *> r1,r2;
    make_dfs_list(root1,r1);
    make_dfs_list(root2,r2);
    mark(root,white);
    mark(root2,black);
    for(int i = 0;i < r1.size();i++)
        for(int j = 0;j < (rt[r1[i] -> rt_id] -> link_info).size();j++)
            if((rt[r1[i] -> rt_id] -> link_info)[j].type == ptp && mp[(rt[r1[i] -> rt_id] -> link_info)[j].link_id] -> color == black && dis > mp[(rt[r1[i] -> rt_id] -> link_info)[j].link_id] -> distance + r1[i] -> distance)
                {
                    dis = mp[(rt[r1[i] -> rt_id] -> link_info)[j].link_id] -> distance + r1[i] -> distance;
                    op = mp[(rt[r1[i] -> rt_id] -> link_info)[j].link_id];
                    ans = r1[i];
                }
    mark(root2,white);
    if(ans){
        string v1 = ans -> rt_id,v2 = op -> rt_id;
        v1.erase(0,6);
        v2.erase(0,6);
        string v3 = root1 -> rt_id,v4 = root2 -> rt_id;
        v3.erase(0,6);
        v4.erase(0,6);
        set<int> t;
        t.insert(stoi(v1));
        t.insert(stoi(v2));
        t.insert(stoi(v3));
        t.insert(stoi(v4));
        vector<int> num(t.begin(),t.end());
        if(num[2] - num[0] < M)
            return NULL;
    }
    if(dis > 3)
        return NULL;
    return ans;
}


void make_dfs_list(struct node *root,vector<struct node *> &r){
    if(!root)
        return;
    r.push_back(root);
    for(int i = 0;i < (root -> children).size();i++)
        make_dfs_list((root -> children)[i],r);
}

void make_net(set<string> &net,struct node *root){
    vector<struct node *> nums;
    make_dfs_list(root,nums);
    for(int i = 0;i < nums.size();i++)
        for(int j = 0;j < (rt[nums[i] -> rt_id] -> link_info).size();j++)
            if((rt[nums[i] -> rt_id] -> link_info)[j].type == stb){
				stringstream ss((rt[nums[i] -> rt_id] -> link_info)[j].link_id);
				string prefix,s;
				int cnt=0;
				while(getline(ss,s,'.')){
					prefix+=s;
					prefix+=".";
					cnt++;
					if(cnt==3)
						break;
				}
				prefix+="0";
                prefix+="/24";
                net.insert(prefix);
            }        
}

void handle_all_node(){
    for(int i = 0;i < nodebase.size();i++){
        dijk_pq2(nodebase[i]);
        if(!network.size())
            make_net(network,nodebase[i]);
        int n = (nodebase[i] -> children).size();
        for(int j = 0;j < n;j++){
            pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[j] -> rt_id);
            make_net(treenet[t],(nodebase[i] -> children)[j]);
        }
        set<string> path;
        for(int j = 0;j < n;j++)
            for(int k = 0;k < n;k++)
                if(j < k){
                    out = NULL;
                    out = seq((nodebase[i] -> children)[j],(nodebase[i] -> children)[k],nodebase[i]);
                    if(out){
                        struct node *p = out;
                        while(p != nodebase[i]){
                            pair<string,string> t(nodebase[i] -> rt_id,p -> rt_id);
                            if(!subtree[t].size())
                                subtree[t] = (nodebase[i] -> children)[j] -> rt_id;
                            path.insert(p -> rt_id);
                            p = p -> pre;
                        }
                        p = op;
                        while(p != nodebase[i]){
                            pair<string,string> t(nodebase[i] -> rt_id,p -> rt_id);
                            if(!subtree[t].size())
                                subtree[t] = (nodebase[i] -> children)[k] -> rt_id;
                            path.insert(p -> rt_id);
                            p = p -> pre;
                        }
                        p = op;
                        while(p != nodebase[i]){
                            path.insert(p -> rt_id);
                            p = p -> pre;
                        }
                    }
                }
        cout<<path.size()<<endl;
        /*set<string>::iterator it;
        if(nodebase[i] -> rt_id == "1.1.1.2")
            for(it = path.begin();it != path.end();it++)
                cout<<*it<<endl;*/
        if(path.find(host) != path.end()){
            struct node *root = mp[host];
            while(root != nodebase[i] && root -> pre != nodebase[i])
                root = root -> pre;
            for(int j = 0;j < n;j++)
                for(int k = 0;k < n;k++)
                    if(j < k){
                        out = NULL;
                        bknext_hop = NULL;
                        struct node *p = NULL,*cd = NULL;
                        set<string> net;
                        out = seq((nodebase[i] -> children)[j],(nodebase[i] -> children)[k],nodebase[i]);
                        if(out){
                            if(out == mp[host]){
                                bknext_hop = op;
                                pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[k] -> rt_id);
                                net = treenet[t];
                            }
                            else if(op == mp[host]){
                                bknext_hop = out;
                                pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[j] -> rt_id);
                                net = treenet[t];
                            }
                            else{
                                p = out;
                                cd = out;
                                while(p != nodebase[i]){
                                    if(p == mp[host]){
                                        bknext_hop = cd;
                                        pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[k] -> rt_id);
                                        net = treenet[t];
                                        break;
                                    }
                                    else{
                                        cd = p;
                                        p = p -> pre;
                                    }
                                }
                                if(!bknext_hop){
                                    p = op;
                                    cd = op;
                                    while(p != nodebase[i]){
                                        if(p == mp[host]){
                                            bknext_hop = cd;
                                            pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[j] -> rt_id);
                                            net = treenet[t];
                                            break;
                                        }
                                        else{
                                            cd = p;
                                            p = p -> pre;
                                        }
                                    }
                                }
                            }
                            pair<string,string> t1(nodebase[i] -> rt_id,out -> rt_id),t2(nodebase[i] -> rt_id,op -> rt_id),t3(nodebase[i] -> rt_id,host);
                            if(!bknext_hop && (subtree[t3] == subtree[t1] || subtree[t3] == subtree[t2])){
                                bknext_hop = mp[host] -> pre;
                                if(subtree[t3] == subtree[t1]){
                                    pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[k] -> rt_id);
                                    net = treenet[t];
                                }
                                else{
                                    pair<string,string> t(nodebase[i] -> rt_id,(nodebase[i] -> children)[j] -> rt_id);
                                    net = treenet[t];
                                }
                            }
			    if(bknext_hop){
                            	gateway = "";
                            	find_gateway();
                            	pair<string,set<string> > t(gateway,net);
                            	bkroute_addr_node[nodebase[i] -> rt_id].push_back(t);
			    }
                        }
                    }
        }
    }
}


void mark(struct node *root,int color){
	if(!root)
		return;
	root -> color = color;
	for(int i =0; i < root -> children.size();i++)
		mark((root -> children)[i],color);
}


void dump_bkroute_node(){
    for(int i = 0;i < nodebase.size();i++)
        if(bkroute_addr_node[nodebase[i] -> rt_id].size()){
            vector<pair<string,set<string> > > t = bkroute_addr_node[nodebase[i] -> rt_id];
            set<string> net;
            struct node *root = mp[host];
            dijk_pq2(nodebase[i]);
            while(root -> pre != nodebase[i]){
                root = root -> pre;
            }
            make_net(net,root);
            map<string,int> vis;
            string filename = nodebase[i] -> rt_id;
            set<string>::iterator it;
            ofstream fout(filename.c_str()); 
            for(int j = 0;j < t.size();j++)
                for(it = t[j].second.begin();it != t[j].second.end();it++)
                    if(!vis[*it] && net.find(*it) == net.end()){
                        fout<<t[j].first<<"\t"<<*it<<endl;
                        vis[*it] = 1;
                    }
            for(it = network.begin();it != network.end();it++)
                if(!vis[*it] && net.find(*it) == net.end()){
                    fout<<t[0].first<<"\t"<<*it<<endl;
                    vis[*it] = 1;
                }
            fout.close();
        }        
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
