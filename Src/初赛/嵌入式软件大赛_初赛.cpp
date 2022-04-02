#include <iostream>
#include <vector>
#include<map>
#include<algorithm>
#include<cmath>
#include<cstring>
#include<iomanip>
#include<queue>
using namespace std;
typedef long long LL;
const LL inf = 1e18;
int N; int E; int C; int D; int PS; int bst_number = 0; int sat_number = 0; int anscount = 0;
int ans[5005];
int already_has_home[5005];//already_has_home[bst_id]为0表示还没找到家的基站，为1表示已经找到家
int already_has_home2[5005];
int already_research[5005];
int real_dis_to_sat[5005];//real_dis_to_sat[sat_id]表示现在考虑的基站到sat_id卫星的真实距离
int type[5005];//0表示基站，1表示未决定类型的卫星，2表示中转卫星，3表示接收卫星
int type2[5005];
int sat_used_times[5005];//一个卫星连接的基站个数
int expect_target_in_search = -1; int shortest_listp = 0;
int shortest_path[5005];
int can_be_farest[5005];
vector<int>route[6000];
vector<int>route2[6000];
vector<int>accessible_sat_id[5005]; //一个vector存储一个基站能够到达的所有卫星，用于在其中选择最合适的作为其接收卫星
struct Footprint
{
	int total = 0;//能到达这个卫星的（还没找到家的）基站的总数，实时更新
	int bst_id[5005];
	int bst_dis[5005];
	LL sum_dis = 0;//能到达这个卫星的（还没找到家的）所有基站到此的距离总和，实时更新
	void add(int id, int dis)//增加一个新到达的基站记录
	{
		bst_id[id] = 1;
		bst_dis[id] = dis;
		sum_dis += dis;
		total++;
	}
	void update_dis(int id, int new_dis)//用更短的距离更新一个基站的已有记录
	{
		if (bst_id[id] == 1)
		{
			sum_dis -= bst_dis[id];
			sum_dis += new_dis;
			bst_dis[id] = new_dis;
		}
		else if (bst_id[id] == 0)
		{
			bst_id[id] = 1;
			bst_dis[id] = new_dis;
			sum_dis += new_dis;
			total++;
		}
	}
};
struct Satellite
{
	int id;
	Footprint footprint;//第i个基站向外bfs时，到达这个卫星，就在此设置footprint.bst_id[i]=1表明来过，并留下到此的距离footprint.bst_dis[i]
}sat[5005];//包含所有结点，基站也在其中
struct Node//邻接点
{
	int id;
	LL dis;
	int target_sat_id = -1;//对每条已经被征用过的边，标记一下此边通向的目标接收卫星。-1表示没有基站征用过这条边
	int target_sat_id2 = -1;
	Node(int ID, LL DIS, int Target_sat_id = -1, int Target_sat_id2 = -1)
	{
		id = ID; dis = DIS; target_sat_id = Target_sat_id; target_sat_id2 = Target_sat_id2;
	}
	~Node(){}
};
struct List_node//单向链表的结点
{
	int bst_id;
	int expect_sat;
	List_node *next;
	List_node(int id, int sat_id)
	{
		bst_id = id;
		expect_sat = sat_id;
		next = NULL;
	}
};
struct Bst_list//试图把基站的考虑顺序串成一个链表
{
	List_node *head = NULL;
	List_node *tail = NULL;
	void insert_after_head(int id, int sat_id)
	{
		if (head == NULL)
		{
			head = new List_node(id, sat_id);
			tail = head;
		}
		else if (head->next == NULL)
		{
			List_node *q = new List_node(id, sat_id);
			head->next = q;
			tail = head->next;
		}
		else
		{
			List_node *q = new List_node(id, sat_id);
			q->next = head->next;
			head->next = q;
		}
	}
	void push_back(int id, int sat_id)
	{
		if (head == NULL)
		{
			head = new List_node(id, sat_id);
			tail = head;
		}
		else
		{
			List_node *q = new List_node(id, sat_id);
			tail->next = q;
			tail = tail->next;
		}
	}
}bst_list, bst_list2;
bool cmp(const Node a, const Node b)
{
	return a.id < b.id;
}
vector<Node>G[6000];//用邻接表实现图
int edge_target(int from, int to)//查找一条边通向哪个接收卫星
{
	for (int i = 0; i < G[from].size(); i++)
	{
		if (G[from][i].id == to)
		{
			return G[from][i].target_sat_id;
		}
	}
	return -1;
}
void set_edge_target(int u, int v, int Target) //设置一条边所通向的接收卫星
{
	for (int i = 0; i < G[u].size(); i++)
	{
		if (G[u][i].id == v)
		{
			G[u][i].target_sat_id = Target;
			break;
		}
	}
	for (int i = 0; i < G[v].size(); i++)
	{
		if (G[v][i].id == u)
		{
			G[v][i].target_sat_id = Target;
			break;
		}
	}
}
int edge_target2(int from, int to)
{
	for (int i = 0; i < G[from].size(); i++)
	{
		if (G[from][i].id == to)
		{
			return G[from][i].target_sat_id2;
		}
	}
	return -1;
}
void set_edge_target2(int u, int v, int target)
{
	for (int i = 0; i < G[u].size(); i++)
	{
		if (G[u][i].id == v)
		{
			G[u][i].target_sat_id2 = target;
			break;
		}
	}
	for (int i = 0; i < G[v].size(); i++)
	{
		if (G[v][i].id == u)
		{
			G[v][i].target_sat_id2 = target;
			break;
		}
	}
}
int the_distance(int from, int to)//查询一条边的长度
{
	for (int i = 0; i < G[from].size(); i++)
	{
		if (G[from][i].id == to)
		{
			return G[from][i].dis;
		}
	}
	return -1;
}
void all_bst_bfs()//所有基站向外bfs，在能到达的卫星处留下footprint，这样以来卫星就记录了可达的所有基站
{
	int visited[5005];
	for (int i = 0; i < N; i++) //由于多次调用此函数，所以需要先清空
	{
		if (type[i] != 0)
		{
			sat[i].footprint.total = 0;
			sat[i].footprint.sum_dis = 0;
		}
		else
		{
			accessible_sat_id[i].clear();
		}
	}
	for (int i = 0; i < N; i++)//这里的i为基站id
	{
		if (type[i] != 0)continue; //排除卫星，只以基站为源点进行bfs
		memset(visited, 0, sizeof(visited));
		queue<Node>q;
		Node u(i, 0); visited[i] = 1;
		q.push(u);
		while (!q.empty())
		{
			Node v = q.front(); q.pop();
			for (int j = 0; j < G[v.id].size(); j++)
			{
				if (type[G[v.id][j].id] == 0)continue; //基站不能走到基站
				if (visited[G[v.id][j].id] == 0)
				{
					if (v.dis + G[v.id][j].dis>D)continue;  //超出路径长度约束
					visited[G[v.id][j].id] = 1;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					sat[G[v.id][j].id].footprint.add(i, v.dis + G[v.id][j].dis); //在此卫星留下足迹
					q.push(a);
					accessible_sat_id[i].push_back(G[v.id][j].id);//将基站i "能到达的" 所有卫星的id都记录下来
				}
				else if (visited[G[v.id][j].id] == 1)//试图让bfs能得到最短路径树
				{
					if (v.dis + G[v.id][j].dis > sat[G[v.id][j].id].footprint.bst_dis[i])continue;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);//（如果这时队列中有相同的结点，会多耗时间
					sat[G[v.id][j].id].footprint.update_dis(i, v.dis + G[v.id][j].dis);
					q.push(a);
				}
			}
			v.~Node();
		}
	}
}
// 当为一个基站找合适的接收卫星时，需要对它所能够到达的所有卫星按下面的规则进行排序，并从队首的卫星开始寻找一个合法可用的
// 下面四个规则大同小异，效果略有不同
bool cmp_Alternative(int a, int b)  
{
	if (type[a] == 3 && type[b] != 3)return true;//一个卫星搜索到一个type为3的卫星，不顾距离多远而直接过去（不一定合理）
	if (type[b] == 3 && type[a] != 3)return false;
	if (type[a] == 3 && type[b] == 3)return real_dis_to_sat[a]<real_dis_to_sat[b];//如果a和b都已经是接收卫星，基站应该直接选离自己近的那个

	///////当a和b都是未安排过身份的卫星时
	if (sat[a].footprint.total > sat[b].footprint.total)return true;//优先选取能管辖更多基站的卫星作为接收卫星
	if (sat[a].footprint.total < sat[b].footprint.total)return false;
	return sat[a].footprint.sum_dis < sat[b].footprint.sum_dis;
}
bool cmp_Alternative2(int a, int b)
{
	if (type[a] == 3 && type[b] != 3)return true;
	if (type[b] == 3 && type[a] != 3)return false;
	if (type[a] == 3 && type[b] == 3)
	{
		return real_dis_to_sat[a] < real_dis_to_sat[b];//不一定合理
	}
	///////当a和b都是未安排过身份的卫星时
	return real_dis_to_sat[a] < real_dis_to_sat[b];
}
bool cmp_Alternative3(int a, int b)
{
	if (type[a] == 3 && type[b] != 3)return true;
	if (type[b] == 3 && type[a] != 3)return false;
	if (type[a] == 3 && type[b] == 3)
	{
		if (sat_used_times[b] == 0 && sat_used_times[a] > sat_used_times[b])return true;
		if (sat_used_times[a] == 0 && sat_used_times[b] > sat_used_times[a])return false;
		if (sat_used_times[b] == 1 && sat_used_times[a] > sat_used_times[b])
		{
			return true;
		}
		if (sat_used_times[a] == 1 && sat_used_times[b] > sat_used_times[a])
		{
			return false;
		}
		if (sat_used_times[b] == 2 && sat_used_times[a] > sat_used_times[b])return true;
		if (sat_used_times[a] == 2 && sat_used_times[b] > sat_used_times[a])return false;
		return real_dis_to_sat[a] < real_dis_to_sat[b];

	}
	///////当a和b都是未安排过身份的卫星时
	if (sat_used_times[a] > sat_used_times[b])return true;
	if (sat_used_times[b] > sat_used_times[a])return false;
	return real_dis_to_sat[a] < real_dis_to_sat[b];
}
bool cmp_Alternative4(int a, int b)
{
	if (type2[a] == 3 && type2[b] == 3)
	{
		return real_dis_to_sat[a] < real_dis_to_sat[b];

	}
	if (type2[a] == 3 && type2[b] != 3)
	{
		if (type[b] == 3)
		{
			if (sat_used_times[b] < 14)return true;
			return real_dis_to_sat[a] < real_dis_to_sat[b];
		}
		if (type[b] != 3)
		{
			return true;
		}
	}
	if (type2[b] == 3 && type2[a] != 3)
	{
		if (type[a] == 3)
		{
			if (sat_used_times[a] < 14)return true;
			return real_dis_to_sat[a] < real_dis_to_sat[b];
		}
		if (type[a] != 3)
		{
			return false;
		}
	}
	if (type2[a] != 3 && type2[b] != 3)
	{
		if (type[a] == 3 && type[b] == 3)
		{
			if (sat_used_times[a] == sat_used_times[b])return real_dis_to_sat[a] < real_dis_to_sat[b];
			return sat_used_times[a]>sat_used_times[b];
			if (sat_used_times[b] < 2 && sat_used_times[a] > sat_used_times[b])
			{
				return true;
			}
			if (sat_used_times[a]  <2 && sat_used_times[b] > sat_used_times[a])
			{
				return false;
			}
			return real_dis_to_sat[a] < real_dis_to_sat[b];
		}
		if (type[a] == 3 && type[b] != 3)
		{
			return true;
		}
		if (type[a] != 3 && type[b] == 3)
		{
			return false;
		}
		if (type[a] != 3 && type[b] != 3)
		{
			return real_dis_to_sat[a] < real_dis_to_sat[b];
		}
	}
	if (sat_used_times[a] > sat_used_times[b])return true;
	if (sat_used_times[a] < sat_used_times[b])return false;
	return real_dis_to_sat[a] < real_dis_to_sat[b];
}

struct Node_dij //Dijkstra的结点
{
	int dis;
	int id;
	Node_dij(int Dis, int ID)
	{
		dis = Dis; id = ID;
	}
	bool operator<(const Node_dij&a)const
	{
		return dis>a.dis;
	}
};
void Dij(int u_id) //Dijkstra算法求基站u_id到其他所有结点（包括基站）的距离
{
	int visited[5005];
	memset(visited, 0, sizeof(visited));
	for (int i = 0; i < N; i++)shortest_path[i] = 1e9;
	priority_queue<Node_dij>q;
	shortest_path[u_id] = 0;
	Node_dij u(0, u_id);
	q.push(u);
	while (!q.empty())
	{
		Node_dij v = q.top(); q.pop();
		if (visited[v.id] == 0)
		{
			visited[v.id] = 1;
			for (int j = 0; j < G[v.id].size(); j++)
			{
				if (shortest_path[v.id] + G[v.id][j].dis < shortest_path[G[v.id][j].id])
				{
					shortest_path[G[v.id][j].id] = shortest_path[v.id] + G[v.id][j].dis;
					if (type[G[v.id][j].id] != 0) //路径不能经过基站
					{
						Node_dij u(shortest_path[G[v.id][j].id], G[v.id][j].id);
						q.push(u);
					}
				}
			}
		}
	}
}
struct shortest_list_node
{
	int bst_id;
	int dis_to_source;
	shortest_list_node(int id, int dis)
	{
		bst_id = id; dis_to_source = dis;
	}
};
vector<shortest_list_node>shortest_list;
bool cmp_shortest_list(shortest_list_node a, shortest_list_node b)
{
	return a.dis_to_source > b.dis_to_source;
}

//寻求一条从基站i到卫星sat_id的(无冲突)路径，保存在ans[]中，其中ans[0]==sat_id且ans[ansp-1]为bst_id(倒叙)，并返回ansp，失败则返回-1
int bfs_with_target(int i, int sat_id, int research_flag = 0)
{
	int visited[5005]; int flag = 0;
	int father_id[5005]; int real_dis[5005];
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(real_dis, -1, sizeof(real_dis));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty())
	{
		Node v = q.front(); q.pop();
		for (int j = 0; j < G[v.id].size(); j++)
		{
			if (type[G[v.id][j].id] == 0)continue;
			int this_target = edge_target(v.id, G[v.id][j].id);
			if (this_target != -1 && this_target != sat_id&&research_flag == 0)
			{
				continue;
			}
			//有路径冲突的边直接不走
			if (research_flag == 1 && this_target != -1 && this_target != sat_id&&v.id != i)
			{
				int other_use_this_edge = 0;
				for (int x = 0; x < N; x++)
				{
					if (type[x] == 0 && x != i)
					{
						for (int w = 0; w + 1 < route[x].size() && route[x][w + 1] != -1; w++)
						{
							if (route[x][w] == v.id&&route[x][w + 1] == G[v.id][j].id || route[x][w] == G[v.id][j].id&&route[x][w + 1] == v.id)
							{
								other_use_this_edge = 1; break;
							}
						}
					}
					if (other_use_this_edge == 1)break;
				}
				if (other_use_this_edge == 1)
				{
					continue;
				}
			}
			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)continue;
				if (G[v.id][j].id == sat_id)//成功到达了目标，不用沿着这里继续搜索
				{
					flag = 1;
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 3)//不是目标卫星的接收卫星，不放在路径树中
				{
					visited[G[v.id][j].id] = 1;
					continue;
				}
				if (type[G[v.id][j].id] == 2 || type[G[v.id][j].id] == 1)
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
			else if (visited[G[v.id][j].id] == 1)
			{
				if (v.dis + G[v.id][j].dis > real_dis[G[v.id][j].id])continue;
				if (G[v.id][j].id == sat_id)
				{
					flag = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 3)continue;
				if (type[G[v.id][j].id] == 2 || type[G[v.id][j].id] == 1)
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
		}
		v.~Node();
	}
	if (flag == 0)return -1;
	int ansp = 0; int find = sat_id;
	while (find != i)
	{
		ans[ansp++] = find;
		find = father_id[find];
	}
	ans[ansp++] = find;
	return ansp;
}

void keep_type_correct()
{
	int reset_type[5005];
	for (int x = 0; x < N; x++)
	{
		if (type[x] == 0)reset_type[x] = 0;
		else reset_type[x] = 1;
	}
	for (int x = 0; x < N; x++)//保持卫星身份的正确性
	{
		if (type[x] == 0)
		{
			for (int j = 0; j < route[x].size() && route[x][j] != -1; j++)
			{
				if (route[x][j + 1] != -1)
				{
					reset_type[route[x][j]] = 2;
				}
				else reset_type[route[x][j]] = 3;
			}
		}
	}
	for (int x = 0; x < N; x++)
	{
		type[x] = reset_type[x];
	}
}
void keep_type2_correct()
{
	int reset_type2[5005];
	for (int x = 0; x < N; x++)
	{
		if (type2[x] == 0)reset_type2[x] = 0;
		else reset_type2[x] = 1;
	}
	for (int x = 0; x < N; x++)//保持卫星身份的正确性
	{
		if (type2[x] == 0)
		{
			for (int j = 0; j < route2[x].size() && route2[x][j] != -1; j++)
			{
				if (route2[x][j + 1] != -1)
				{
					reset_type2[route2[x][j]] = 2;
				}
				else reset_type2[route2[x][j]] = 3;
			}
		}
	}
	for (int x = 0; x < N; x++)
	{
		type2[x] = reset_type2[x];
	}
}
void keep_target_correct()//时间代价较高
{
	for (int i = 0; i < N; i++)
	{
		for (int j = 0; j < G[i].size(); j++)
		{
			G[i][j].target_sat_id = -1;
		}
	}
	for (int i = 0; i < N; i++)
	{
		if (type[i] == 0 && route[i].size()>1)
		{
			int j;
			for (j = 0; j + 1 < route[i].size() && route[i][j + 1] != -1; j++);
			set_edge_target(i, route[i][0], route[i][j]);
			for (int w = 1; w < route[i].size() && route[i][w] != -1; w++)
			{
				set_edge_target(route[i][w - 1], route[i][w], route[i][j]);
			}
		}
	}
}
void keep_target2_correct()
{
	for (int i = 0; i < N; i++)
	{
		for (int j = 0; j < G[i].size(); j++)
		{
			G[i][j].target_sat_id2 = -1;
		}
	}
	for (int i = 0; i < N; i++)
	{
		if (type2[i] == 0 && route2[i].size()>1)
		{
			int j;
			for (j = 0; j + 1 < route2[i].size() && route2[i][j + 1] != -1; j++);
			set_edge_target2(i, route2[i][0], route2[i][j]);
			for (int w = 1; w < route2[i].size() && route2[i][w] != -1; w++)
			{
				set_edge_target2(route2[i][w - 1], route2[i][w], route2[i][j]);
			}
		}
	}
}
//为基站i寻找一个合适的接收卫星，并记录下这条合法路径，同时维护边的target等信息
void search(int i, int expect_target)
{
	if (type[i] != 0)return;
	if (already_has_home[i] == 1)return;
	int visited[5005]; int exist_in_alternative[5005];  int father_id[5005];
	int ansp = 0;
	expect_target_in_search = expect_target;
	vector<int>alternative_sat; //备选卫星列表
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(exist_in_alternative, 0, sizeof(exist_in_alternative));
	memset(real_dis_to_sat, -1, sizeof(real_dis_to_sat));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty()) //bfs搜索，记录每个结点在bfs树中的父节点，并求得i到其他结点的距离
	{
		Node v = q.front(); q.pop();
		for (int j = 0; j < G[v.id].size(); j++)
		{
			if (type[G[v.id][j].id] == 0)
			{
				continue;
			}
			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)//如果在限制距离内，无法到达G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}

			}
			else if (visited[G[v.id][j].id] == 1)//试图让bfs能得到最短路径树
			{
				if (v.dis + G[v.id][j].dis > real_dis_to_sat[G[v.id][j].id])continue;
				int flag = 0; int lost_bst_id;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
		}
		v.~Node();
	}

	//将bfs过程中搜索到的备选卫星，按自定义规则进行排序，优的在前
	sort(alternative_sat.begin(), alternative_sat.end(), cmp_Alternative);

	int check = 0;
	//原来是依次尝试接收卫星是否可行，现改为无视路径冲突约束，直接选取队首的为接收卫星
	for (int p = 0; p < alternative_sat.size(); p++)
	{
		int find = alternative_sat[p];
		ansp = 0; int target;
		while (find != i)
		{
			ans[ansp++] = find;
			find = father_id[find];
		}
		ans[ansp++] = find;
		already_has_home[i] = 1;
		for (int w = 0; w < N; w++)//告诉所有卫星(包括现在指定的接收卫星)，此基站已经有家，更新total和sum_dis
		{
			if (sat[w].footprint.bst_id[i] != 0)
			{
				sat[w].footprint.sum_dis -= sat[w].footprint.bst_dis[i];
				sat[w].footprint.bst_id[i] = 0;
				sat[w].footprint.total--;
			}
		}
		type[ans[0]] = 3;//确定接收卫星身份
		for (int w = 0; w < N; w++)//让 "能到达" 这个接收卫星的其他还没有家的基站紧跟在表头后面
		{
			if (sat[ans[0]].footprint.bst_id[w] != 0 && already_has_home[w] == 0)
			{
				bst_list.insert_after_head(w, ans[0]);
			}
		}
		for (int w = ansp - 2; w >= 1; w--)//确定沿途卫星为中转卫星身份
		{
			type[ans[w]] = 2;
		}

		for (int w = ansp - 2; w >= 0; w--)
		{
			route[i].push_back(ans[w]);
		}
		route[i].push_back(-1);
		anscount++; check = 1;
		break;
	}
}

// 确定基站的考虑顺序，并按顺序为每个基站找到合适的接收卫星
void search_all()
{
	int flag = 1;
	while (flag == 1) //flag==1意味着仍有基站还未找到家，这样设计是为了处理多个不联通子网的情况
	{
		flag = 0; shortest_listp = 0;
		memset(can_be_farest, 0, sizeof(can_be_farest));
		shortest_list.clear();
		
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0) //i是一个还没有找到家的基站
			{
				Dij(i);  //求其他所有结点到i的最短距离
				int maxdis = -1; int maxj;
				for (int j = 0; j < N; j++) //找到基站i可达的且距离最远的基站maxj
				{
					if (type[j] == 0 && already_has_home[j] == 0)
					{
						if (shortest_path[j] > maxdis&&shortest_path[j]<1e9)
						{
							maxdis = shortest_path[j];
							maxj = j;
						}
					}
				}
				can_be_farest[maxj] ++;
			}
		}
		//找到充当“最远基站”最多次的基站farest_max_id
		int farest_max_times = 1e9; int farest_max_id;
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && can_be_farest[i] != 0)
			{
				//cout << "基站 " << i << " 充当最远基站共" << can_be_farest[i] << "次\n";
				if (can_be_farest[i] <= farest_max_times)
				{
					farest_max_times = can_be_farest[i];
					farest_max_id = i;
				}
			}
		}
		//求此基站所能够到达的所有结点的最短距离
		Dij(farest_max_id);
		
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0 && shortest_path[i]<1e9)
			{
				shortest_list_node u(i, shortest_path[i]);
				shortest_list.push_back(u);
			}
		}
		//基站按距离从远到近进行排序，这就是基站的考虑顺序
		sort(shortest_list.begin(), shortest_list.end(), cmp_shortest_list);

		while (shortest_listp < shortest_list.size()) //依次考虑这些基站
		{
			if (already_has_home[shortest_list[shortest_listp].bst_id] == 0) //已经规划过的基站不管
			{
				bst_list.push_back(shortest_list[shortest_listp].bst_id, -1); //把尚未规划过的基站插入链表末尾
				while (bst_list.head != NULL)
				{
					//为这个基站找一个合适的接收卫星，保存路径信息，并让能够到达同一个接收卫星的基站插入此链表中
					search(bst_list.head->bst_id, bst_list.head->expect_sat);
					bst_list.head = bst_list.head->next;
				}
			}
			shortest_listp++;
		}
		//检查是否还有基站未规划
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0)
			{
				flag = 1; break;
			}
		}
	}


}

//为基站i进行重新规划，需要符合路径不冲突约束
void research(int i, int cmp_flag = 2)
{
	if (type[i] != 0)return;
	if (already_research[i] == 1)return;
	int visited[5005]; int exist_in_alternative[5005];  int father_id[5005];
	int ansp = 0;
	vector<int>alternative_sat;//在基站i向外bfs过程中找到的几个适合设置为接收卫星的卫星id
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(exist_in_alternative, 0, sizeof(exist_in_alternative));
	memset(real_dis_to_sat, -1, sizeof(real_dis_to_sat));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty())
	{
		Node v = q.front(); q.pop();
		for (int j = 0; j < G[v.id].size(); j++)
		{
			if (type[G[v.id][j].id] == 0)
			{
				continue;
			}
			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)//如果在限制距离内，无法到达G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}

			}
			else if (visited[G[v.id][j].id] == 1)
			{
				if (v.dis + G[v.id][j].dis > real_dis_to_sat[G[v.id][j].id])continue;
				int flag = 0; int lost_bst_id;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
		}
		v.~Node();
	}
	if (cmp_flag == 2)
	{
		sort(alternative_sat.begin(), alternative_sat.end(), cmp_Alternative2);
	}
	else if (cmp_flag == 3)
	{
		sort(alternative_sat.begin(), alternative_sat.end(), cmp_Alternative3);
	}

	int check = 0;
	//依次尝试备选接收卫星，直到找到第一个合法可行的
	for (int p = 0; p < alternative_sat.size(); p++)
	{
		int find = alternative_sat[p];
		int flag = 0;
		ansp = 0; int target;
		while (find != i)
		{
			ans[ansp++] = find;
			find = father_id[find];
			target = edge_target(find, ans[ansp - 1]);
			if (target != -1 && target != ans[0] && find != i)//已经有基站征用了这条边，且接收卫星不一样
			{
				int other_use_this_edge = 0;
				for (int x = 0; x < N; x++)
				{
					if (type[x] == 0 && x != i)
					{
						for (int j = 0; j + 1 < route[x].size() && route[x][j + 1] != -1; j++)
						{
							if (route[x][j] == find&&route[x][j + 1] == ans[ansp - 1] || route[x][j] == ans[ansp - 1] && route[x][j + 1] == find)
							{
								other_use_this_edge = 1; break;
							}
						}
					}
					if (other_use_this_edge == 1)break;
				}
				if (other_use_this_edge == 1)
				{
					flag = 1; break;
				}
			}
		}
		if (flag == 1) //目前路径不可行，但不意味着这个接收卫星不可选
		{
			ansp = bfs_with_target(i, alternative_sat[p], 1); //尝试寻找一条从基站i到此接收卫星的合法路径
			if (ansp == -1) //没有找到
			{
				continue;
			}
		}
		else //此接收卫星可选，且路径合法
		{
			ans[ansp++] = find;
		}
		already_research[i] = 1;

		route[i].clear();
		keep_type_correct(); //维护结点身份的正确性

		type[ans[0]] = 3;//确定接收卫星身份
		for (int w = ansp - 2; w >= 1; w--)//确定沿途卫星为中转卫星身份
		{
			type[ans[w]] = 2;
		}
		for (int w = ansp - 1; w >= 1; w--)//给路径上每条边打上标记（接收卫星的id
		{
			set_edge_target(ans[w], ans[w - 1], ans[0]);
		}
		for (int w = ansp - 2; w >= 0; w--)
		{
			route[i].push_back(ans[w]);
		}
		route[i].push_back(-1);
		check = 1;
		break;
	}
	if (check == 0)//遍历完整个备选队列都找不到能作为接收卫星的（到达的路上都发生了冲突）
	{
		//直接选取与此基站直接相邻的卫星，并修改其他已规划过的路径，消除冲突
		int closest_sat = G[i][0].id; int closest_dis = G[i][0].dis;
		for (int x = 0; x < G[i].size(); x++)
		{
			if (G[i][x].dis < closest_dis)
			{
				closest_sat = G[i][x].id;
				closest_dis = G[i][x].dis;
			}
		}
		type[closest_sat] = 3;
		already_research[i] = 1;
		anscount++;
		route[i].push_back(closest_sat); route[i].push_back(-1);
		set_edge_target(i, closest_sat, closest_sat);
		for (int x = 0; x < N; x++)
		{
			if (type[x] == 0)
			{
				for (int j = 0; j < route[x].size() && route[x][j] != -1; j++)
				{
					if (route[x][j] == closest_sat)
					{
						route[x][j + 1] = -1;//直接到此为止，把后路断了
						set_edge_target(x, route[x][0], closest_sat);
						for (int k = 1; k <= j; k++)
						{
							set_edge_target(route[x][k - 1], route[x][k], closest_sat);
						}
					}
				}
			}
		}
		keep_type_correct();
	}
}
//所有基站重新规划，cmp_flag表示使用哪一个排序规则
void research_all(int cmp_flag = 2)
{
	for (int i = 0; i < N; i++)
	{
		if (type[i] == 0)
		{
			research(i, cmp_flag);
		}
	}
}
void count_sat_times(int route_flag = 0)
{
	memset(sat_used_times, 0, sizeof(sat_used_times));
	if (route_flag == 0)
	{
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0)
			{
				int j;
				for (j = 0; j + 1 < route[i].size() && route[i][j + 1] != -1; j++);
				sat_used_times[route[i][j]]++;
			}
		}
	}
	else if (route_flag == 2)
	{
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0)
			{
				int j;
				for (j = 0; j + 1 < route2[i].size() && route2[i][j + 1] != -1; j++);
				sat_used_times[route2[i][j]]++;
			}
		}
	}
}
int bfs_with_target2(int i, int sat_id)//寻求一条从基站i到卫星sat_id的(无冲突)路径，保存在ans[]中，其中ans[0]==sat_id且ans[ansp-1]为bst_id(倒叙)，并返回ansp，失败则返回-1
{
	int visited[5005]; int flag = 0;
	int father_id[5005]; int real_dis[5005];
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(real_dis, -1, sizeof(real_dis));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty())
	{
		Node v = q.front(); q.pop();
		for (int j = 0; j < G[v.id].size(); j++)
		{
			if (type2[G[v.id][j].id] == 0)continue;
			int this_target2 = edge_target2(v.id, G[v.id][j].id);
			if (this_target2 != -1 && this_target2 != sat_id)
			{
				continue;
			}
			//有路径冲突的边直接不走

			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)continue;
				if (G[v.id][j].id == sat_id)//成功到达了目标，不用沿着这里继续搜索
				{
					flag = 1;
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 3)//不是目标卫星的接收卫星，不放在路径树中
				{
					visited[G[v.id][j].id] = 1;
					continue;
				}
				if (type2[G[v.id][j].id] == 2 || type2[G[v.id][j].id] == 1)
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
			else if (visited[G[v.id][j].id] == 1)
			{
				if (v.dis + G[v.id][j].dis > real_dis[G[v.id][j].id])continue;
				if (G[v.id][j].id == sat_id)
				{
					flag = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 3)continue;
				if (type2[G[v.id][j].id] == 2 || type2[G[v.id][j].id] == 1)
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
		}
		v.~Node();
	}
	if (flag == 0)return -1;
	int ansp = 0; int find = sat_id;
	while (find != i)
	{
		ans[ansp++] = find;
		find = father_id[find];
	}
	ans[ansp++] = find;
	return ansp;
}
void remake_search(int i)
{
	if (type2[i] != 0)return;
	if (already_has_home2[i] == 1)return;
	int visited[5005]; int exist_in_alternative[5005];  int father_id[5005];
	int ansp = 0;
	vector<int>alternative_sat;//在基站i向外bfs过程中找到的几个适合设置为接收卫星的卫星id
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(exist_in_alternative, 0, sizeof(exist_in_alternative));
	memset(real_dis_to_sat, -1, sizeof(real_dis_to_sat));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty())
	{
		Node v = q.front(); q.pop();
		for (int j = 0; j < G[v.id].size(); j++)
		{
			if (type2[G[v.id][j].id] == 0)
			{
				continue;
			}
			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)//如果在限制距离内，无法到达G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type2[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}

			}
			else if (visited[G[v.id][j].id] == 1)
			{
				if (v.dis + G[v.id][j].dis > real_dis_to_sat[G[v.id][j].id])continue;
				int flag = 0; int lost_bst_id;
				if (type2[G[v.id][j].id] == 3)//G[v.id][j].id已经被确定过为接收卫星，直接列入备选，停止这条分支的搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 2)//如果已经确定为中转卫星，则不可能列入备选，可以沿着这条分支继续搜索
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 1)//如果是未安排过类型的卫星，列入备选，可以沿着这条分支搜索
				{
					if (exist_in_alternative[G[v.id][j].id] == 0)
					{
						alternative_sat.push_back(G[v.id][j].id);
						exist_in_alternative[G[v.id][j].id] = 1;
					}
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
			}
		}
		v.~Node();
	}

	sort(alternative_sat.begin(), alternative_sat.end(), cmp_Alternative4);

	int check = 0;
	for (int p = 0; p < alternative_sat.size(); p++)
	{
		int find = alternative_sat[p];
		int flag = 0;
		ansp = 0; int target2;
		while (find != i)
		{
			ans[ansp++] = find;
			find = father_id[find];
			target2 = edge_target2(find, ans[ansp - 1]);
			if (target2 != -1 && target2 != ans[0])//已经有基站征用了这条边，且接收卫星不一样
			{
				flag = 1; break;
			}
		}

		if (flag == 1)
		{
			ansp = bfs_with_target2(i, alternative_sat[p]);
			if (ansp == -1)
			{
				continue;
			}
		}
		else
		{
			ans[ansp++] = find;
		}

		already_has_home2[i] = 1;

		type2[ans[0]] = 3;//确定接收卫星身份

		for (int w = ansp - 2; w >= 1; w--)//确定沿途卫星为中转卫星身份
		{
			type2[ans[w]] = 2;
		}
		for (int w = ansp - 1; w >= 1; w--)//给路径上每条边打上标记（接收卫星的id
		{
			set_edge_target2(ans[w], ans[w - 1], ans[0]);
		}
		for (int w = ansp - 2; w >= 0; w--)
		{
			route2[i].push_back(ans[w]);
		}
		route2[i].push_back(-1);
		check = 1;
		break;
	}
	if (check == 0)//遍历完整个备选队列都找不到能作为接收卫星的（到达的路上都发生了冲突）
	{
		int closest_sat = G[i][0].id; int closest_dis = G[i][0].dis;
		for (int x = 0; i < G[i].size(); x++)
		{
			if (G[i][x].dis < closest_dis)
			{
				closest_sat = G[i][x].id;
				closest_dis = G[i][x].dis;
			}
		}
		type2[closest_sat] = 3;//题目没有保证一个基站只连接了一个卫星
		already_has_home2[i] = 1;
		route2[i].push_back(closest_sat); route2[i].push_back(-1);
		set_edge_target2(i, closest_sat, closest_sat);
		for (int x = 0; x < N; x++)
		{
			if (type2[x] == 0)
			{
				for (int j = 0; j < route2[x].size() && route2[x][j] != -1; j++)
				{
					if (route2[x][j] == closest_sat)
					{
						route2[x][j + 1] = -1;//直接到此为止，把后路断了
						set_edge_target2(x, route2[x][0], closest_sat);
						for (int k = 1; k <= j; k++)
						{
							set_edge_target2(route2[x][k - 1], route2[x][k], closest_sat);
						}
					}
				}
			}
		}
		keep_type2_correct();

	}
}
void remake_all(int times = 0)
{
	if (times != 0)
	{
		keep_type2_correct();
		for (int i = 0; i < N; i++)
		{
			type[i] = type2[i];
		}
		count_sat_times(2);
		for (int i = 0; i < N; i++)
		{
			for (int j = 0; j < G[i].size(); j++)
			{
				G[i][j].target_sat_id2 = -1;
			}
		}
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0)
			{
				route2[i].clear();
			}
		}
	}
	else
	{
		keep_type_correct();
		count_sat_times();
	}
	memset(already_has_home2, 0, sizeof(already_has_home2));

	for (int i = 0; i < N; i++)
	{
		if (type[i] == 0)type2[i] = 0;
		else type2[i] = 1;
	}
	if (times % 2 == 0)
	{
		for (int i = N - 1; i >= 0; i--)
		{
			if (type2[i] == 0)
			{
				remake_search(i);
			}
		}
	}
	else if (times % 2 == 1)
	{
		for (int i = 0; i < N; i++)
		{
			if (type2[i] == 0)
			{
				remake_search(i);
			}
		}
	}
}
int main(int argc, char *argv[])
{
	freopen("training-2.txt", "r", stdin);
	freopen("out4.txt", "w", stdout);
	cin >> N >> E >> C >> D >> PS;
	if (D > 475)D = 475; //当路径长度上限D过大时，相当于几乎没有路径长度约束，将导致传输功耗过大，总成本更大
	for (int i = 0; i < N; i++)
	{
		cin >> type[i];
		if (type[i] == 1) //读入所有结点的身份，0为基站，1为卫星（暂未分化为接收/中转卫星）
		{
			sat[i].id = i;
			sat_number++;
		}
		else if (type[i] == 0)
		{
			sat[i].id = i;
			bst_number++;
		}
	}
	int u, v; LL dis;
	//建图（邻接表）
	for (int i = 0; i < E; i++)
	{
		cin >> u >> v >> dis;
		Node a(u, dis);
		Node b(v, dis);
		G[u].push_back(b);
		G[v].push_back(a);
	}
	for (int i = 0; i < N; i++) //对邻居排序，对结果有少量影响
	{
		sort(G[i].begin(), G[i].end(), cmp);
	}
	//初始时，所有基站还没有找到家
	memset(already_has_home, 0, sizeof(already_has_home));

	//以每个基站为源点进行bfs，在所能到达的卫星处留下自己的id以及距离，并记录这个基站能到达的所有卫星
	all_bst_bfs();

	//确定基站的考虑顺序，并按顺序为每个基站找到合适的接收卫星（先无视路径冲突约束）
	search_all();
	
	for (int i = 0; i < 1; i++)
	{
		memset(already_research, 0, sizeof(already_research));
		//利用第一次规划的信息，将所有基站重新规划一次，保证符合路径不冲突，且优先选择第一次规划的接收卫星
		research_all(2);
	}

	//输出答案
	for (int i = 0; i < N; i++)
	{
		if (type[i] == 0)
		{
			cout << i << " ";
			int j = 0;
			while (j < route[i].size() && route[i][j] != -1)
			{
				cout << route[i][j] << " ";
				j++;
			}
			cout << "\n";
		}
	}
}


