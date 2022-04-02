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
int already_has_home[5005];//already_has_home[bst_id]Ϊ0��ʾ��û�ҵ��ҵĻ�վ��Ϊ1��ʾ�Ѿ��ҵ���
int already_has_home2[5005];
int already_research[5005];
int real_dis_to_sat[5005];//real_dis_to_sat[sat_id]��ʾ���ڿ��ǵĻ�վ��sat_id���ǵ���ʵ����
int type[5005];//0��ʾ��վ��1��ʾδ�������͵����ǣ�2��ʾ��ת���ǣ�3��ʾ��������
int type2[5005];
int sat_used_times[5005];//һ���������ӵĻ�վ����
int expect_target_in_search = -1; int shortest_listp = 0;
int shortest_path[5005];
int can_be_farest[5005];
vector<int>route[6000];
vector<int>route2[6000];
vector<int>accessible_sat_id[5005]; //һ��vector�洢һ����վ�ܹ�������������ǣ�����������ѡ������ʵ���Ϊ���������
struct Footprint
{
	int total = 0;//�ܵ���������ǵģ���û�ҵ��ҵģ���վ��������ʵʱ����
	int bst_id[5005];
	int bst_dis[5005];
	LL sum_dis = 0;//�ܵ���������ǵģ���û�ҵ��ҵģ����л�վ���˵ľ����ܺͣ�ʵʱ����
	void add(int id, int dis)//����һ���µ���Ļ�վ��¼
	{
		bst_id[id] = 1;
		bst_dis[id] = dis;
		sum_dis += dis;
		total++;
	}
	void update_dis(int id, int new_dis)//�ø��̵ľ������һ����վ�����м�¼
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
	Footprint footprint;//��i����վ����bfsʱ������������ǣ����ڴ�����footprint.bst_id[i]=1���������������µ��˵ľ���footprint.bst_dis[i]
}sat[5005];//�������н�㣬��վҲ������
struct Node//�ڽӵ�
{
	int id;
	LL dis;
	int target_sat_id = -1;//��ÿ���Ѿ������ù��ıߣ����һ�´˱�ͨ���Ŀ��������ǡ�-1��ʾû�л�վ���ù�������
	int target_sat_id2 = -1;
	Node(int ID, LL DIS, int Target_sat_id = -1, int Target_sat_id2 = -1)
	{
		id = ID; dis = DIS; target_sat_id = Target_sat_id; target_sat_id2 = Target_sat_id2;
	}
	~Node(){}
};
struct List_node//��������Ľ��
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
struct Bst_list//��ͼ�ѻ�վ�Ŀ���˳�򴮳�һ������
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
vector<Node>G[6000];//���ڽӱ�ʵ��ͼ
int edge_target(int from, int to)//����һ����ͨ���ĸ���������
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
void set_edge_target(int u, int v, int Target) //����һ������ͨ��Ľ�������
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
int the_distance(int from, int to)//��ѯһ���ߵĳ���
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
void all_bst_bfs()//���л�վ����bfs�����ܵ�������Ǵ�����footprint�������������Ǿͼ�¼�˿ɴ�����л�վ
{
	int visited[5005];
	for (int i = 0; i < N; i++) //���ڶ�ε��ô˺�����������Ҫ�����
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
	for (int i = 0; i < N; i++)//�����iΪ��վid
	{
		if (type[i] != 0)continue; //�ų����ǣ�ֻ�Ի�վΪԴ�����bfs
		memset(visited, 0, sizeof(visited));
		queue<Node>q;
		Node u(i, 0); visited[i] = 1;
		q.push(u);
		while (!q.empty())
		{
			Node v = q.front(); q.pop();
			for (int j = 0; j < G[v.id].size(); j++)
			{
				if (type[G[v.id][j].id] == 0)continue; //��վ�����ߵ���վ
				if (visited[G[v.id][j].id] == 0)
				{
					if (v.dis + G[v.id][j].dis>D)continue;  //����·������Լ��
					visited[G[v.id][j].id] = 1;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					sat[G[v.id][j].id].footprint.add(i, v.dis + G[v.id][j].dis); //�ڴ����������㼣
					q.push(a);
					accessible_sat_id[i].push_back(G[v.id][j].id);//����վi "�ܵ����" �������ǵ�id����¼����
				}
				else if (visited[G[v.id][j].id] == 1)//��ͼ��bfs�ܵõ����·����
				{
					if (v.dis + G[v.id][j].dis > sat[G[v.id][j].id].footprint.bst_dis[i])continue;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);//�������ʱ����������ͬ�Ľ�㣬����ʱ��
					sat[G[v.id][j].id].footprint.update_dis(i, v.dis + G[v.id][j].dis);
					q.push(a);
				}
			}
			v.~Node();
		}
	}
}
// ��Ϊһ����վ�Һ��ʵĽ�������ʱ����Ҫ�������ܹ�������������ǰ�����Ĺ���������򣬲��Ӷ��׵����ǿ�ʼѰ��һ���Ϸ����õ�
// �����ĸ������ͬС�죬Ч�����в�ͬ
bool cmp_Alternative(int a, int b)  
{
	if (type[a] == 3 && type[b] != 3)return true;//һ������������һ��typeΪ3�����ǣ����˾����Զ��ֱ�ӹ�ȥ����һ������
	if (type[b] == 3 && type[a] != 3)return false;
	if (type[a] == 3 && type[b] == 3)return real_dis_to_sat[a]<real_dis_to_sat[b];//���a��b���Ѿ��ǽ������ǣ���վӦ��ֱ��ѡ���Լ������Ǹ�

	///////��a��b����δ���Ź���ݵ�����ʱ
	if (sat[a].footprint.total > sat[b].footprint.total)return true;//����ѡȡ�ܹ�Ͻ�����վ��������Ϊ��������
	if (sat[a].footprint.total < sat[b].footprint.total)return false;
	return sat[a].footprint.sum_dis < sat[b].footprint.sum_dis;
}
bool cmp_Alternative2(int a, int b)
{
	if (type[a] == 3 && type[b] != 3)return true;
	if (type[b] == 3 && type[a] != 3)return false;
	if (type[a] == 3 && type[b] == 3)
	{
		return real_dis_to_sat[a] < real_dis_to_sat[b];//��һ������
	}
	///////��a��b����δ���Ź���ݵ�����ʱ
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
	///////��a��b����δ���Ź���ݵ�����ʱ
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

struct Node_dij //Dijkstra�Ľ��
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
void Dij(int u_id) //Dijkstra�㷨���վu_id���������н�㣨������վ���ľ���
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
					if (type[G[v.id][j].id] != 0) //·�����ܾ�����վ
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

//Ѱ��һ���ӻ�վi������sat_id��(�޳�ͻ)·����������ans[]�У�����ans[0]==sat_id��ans[ansp-1]Ϊbst_id(����)��������ansp��ʧ���򷵻�-1
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
			//��·����ͻ�ı�ֱ�Ӳ���
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
				if (G[v.id][j].id == sat_id)//�ɹ�������Ŀ�꣬�������������������
				{
					flag = 1;
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 3)//����Ŀ�����ǵĽ������ǣ�������·������
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
	for (int x = 0; x < N; x++)//����������ݵ���ȷ��
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
	for (int x = 0; x < N; x++)//����������ݵ���ȷ��
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
void keep_target_correct()//ʱ����۽ϸ�
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
//Ϊ��վiѰ��һ�����ʵĽ������ǣ�����¼�������Ϸ�·����ͬʱά���ߵ�target����Ϣ
void search(int i, int expect_target)
{
	if (type[i] != 0)return;
	if (already_has_home[i] == 1)return;
	int visited[5005]; int exist_in_alternative[5005];  int father_id[5005];
	int ansp = 0;
	expect_target_in_search = expect_target;
	vector<int>alternative_sat; //��ѡ�����б�
	memset(visited, 0, sizeof(visited));
	memset(father_id, -1, sizeof(father_id));
	memset(exist_in_alternative, 0, sizeof(exist_in_alternative));
	memset(real_dis_to_sat, -1, sizeof(real_dis_to_sat));
	queue<Node>q;
	Node u(i, 0); visited[i] = 1; father_id[i] = i;
	q.push(u);
	while (!q.empty()) //bfs��������¼ÿ�������bfs���еĸ��ڵ㣬�����i���������ľ���
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
				if (v.dis + G[v.id][j].dis > D)//��������ƾ����ڣ��޷�����G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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
			else if (visited[G[v.id][j].id] == 1)//��ͼ��bfs�ܵõ����·����
			{
				if (v.dis + G[v.id][j].dis > real_dis_to_sat[G[v.id][j].id])continue;
				int flag = 0; int lost_bst_id;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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

	//��bfs�������������ı�ѡ���ǣ����Զ��������������ŵ���ǰ
	sort(alternative_sat.begin(), alternative_sat.end(), cmp_Alternative);

	int check = 0;
	//ԭ�������γ��Խ��������Ƿ���У��ָ�Ϊ����·����ͻԼ����ֱ��ѡȡ���׵�Ϊ��������
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
		for (int w = 0; w < N; w++)//������������(��������ָ���Ľ�������)���˻�վ�Ѿ��мң�����total��sum_dis
		{
			if (sat[w].footprint.bst_id[i] != 0)
			{
				sat[w].footprint.sum_dis -= sat[w].footprint.bst_dis[i];
				sat[w].footprint.bst_id[i] = 0;
				sat[w].footprint.total--;
			}
		}
		type[ans[0]] = 3;//ȷ�������������
		for (int w = 0; w < N; w++)//�� "�ܵ���" ����������ǵ�������û�мҵĻ�վ�����ڱ�ͷ����
		{
			if (sat[ans[0]].footprint.bst_id[w] != 0 && already_has_home[w] == 0)
			{
				bst_list.insert_after_head(w, ans[0]);
			}
		}
		for (int w = ansp - 2; w >= 1; w--)//ȷ����;����Ϊ��ת�������
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

// ȷ����վ�Ŀ���˳�򣬲���˳��Ϊÿ����վ�ҵ����ʵĽ�������
void search_all()
{
	int flag = 1;
	while (flag == 1) //flag==1��ζ�����л�վ��δ�ҵ��ң����������Ϊ�˴���������ͨ���������
	{
		flag = 0; shortest_listp = 0;
		memset(can_be_farest, 0, sizeof(can_be_farest));
		shortest_list.clear();
		
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0) //i��һ����û���ҵ��ҵĻ�վ
			{
				Dij(i);  //���������н�㵽i����̾���
				int maxdis = -1; int maxj;
				for (int j = 0; j < N; j++) //�ҵ���վi�ɴ���Ҿ�����Զ�Ļ�վmaxj
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
		//�ҵ��䵱����Զ��վ�����εĻ�վfarest_max_id
		int farest_max_times = 1e9; int farest_max_id;
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && can_be_farest[i] != 0)
			{
				//cout << "��վ " << i << " �䵱��Զ��վ��" << can_be_farest[i] << "��\n";
				if (can_be_farest[i] <= farest_max_times)
				{
					farest_max_times = can_be_farest[i];
					farest_max_id = i;
				}
			}
		}
		//��˻�վ���ܹ���������н�����̾���
		Dij(farest_max_id);
		
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0 && shortest_path[i]<1e9)
			{
				shortest_list_node u(i, shortest_path[i]);
				shortest_list.push_back(u);
			}
		}
		//��վ�������Զ����������������ǻ�վ�Ŀ���˳��
		sort(shortest_list.begin(), shortest_list.end(), cmp_shortest_list);

		while (shortest_listp < shortest_list.size()) //���ο�����Щ��վ
		{
			if (already_has_home[shortest_list[shortest_listp].bst_id] == 0) //�Ѿ��滮���Ļ�վ����
			{
				bst_list.push_back(shortest_list[shortest_listp].bst_id, -1); //����δ�滮���Ļ�վ��������ĩβ
				while (bst_list.head != NULL)
				{
					//Ϊ�����վ��һ�����ʵĽ������ǣ�����·����Ϣ�������ܹ�����ͬһ���������ǵĻ�վ�����������
					search(bst_list.head->bst_id, bst_list.head->expect_sat);
					bst_list.head = bst_list.head->next;
				}
			}
			shortest_listp++;
		}
		//����Ƿ��л�վδ�滮
		for (int i = 0; i < N; i++)
		{
			if (type[i] == 0 && already_has_home[i] == 0)
			{
				flag = 1; break;
			}
		}
	}


}

//Ϊ��վi�������¹滮����Ҫ����·������ͻԼ��
void research(int i, int cmp_flag = 2)
{
	if (type[i] != 0)return;
	if (already_research[i] == 1)return;
	int visited[5005]; int exist_in_alternative[5005];  int father_id[5005];
	int ansp = 0;
	vector<int>alternative_sat;//�ڻ�վi����bfs�������ҵ��ļ����ʺ�����Ϊ�������ǵ�����id
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
				if (v.dis + G[v.id][j].dis > D)//��������ƾ����ڣ��޷�����G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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
				if (type[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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
	//���γ��Ա�ѡ�������ǣ�ֱ���ҵ���һ���Ϸ����е�
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
			if (target != -1 && target != ans[0] && find != i)//�Ѿ��л�վ�����������ߣ��ҽ������ǲ�һ��
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
		if (flag == 1) //Ŀǰ·�������У�������ζ������������ǲ���ѡ
		{
			ansp = bfs_with_target(i, alternative_sat[p], 1); //����Ѱ��һ���ӻ�վi���˽������ǵĺϷ�·��
			if (ansp == -1) //û���ҵ�
			{
				continue;
			}
		}
		else //�˽������ǿ�ѡ����·���Ϸ�
		{
			ans[ansp++] = find;
		}
		already_research[i] = 1;

		route[i].clear();
		keep_type_correct(); //ά�������ݵ���ȷ��

		type[ans[0]] = 3;//ȷ�������������
		for (int w = ansp - 2; w >= 1; w--)//ȷ����;����Ϊ��ת�������
		{
			type[ans[w]] = 2;
		}
		for (int w = ansp - 1; w >= 1; w--)//��·����ÿ���ߴ��ϱ�ǣ��������ǵ�id
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
	if (check == 0)//������������ѡ���ж��Ҳ�������Ϊ�������ǵģ������·�϶������˳�ͻ��
	{
		//ֱ��ѡȡ��˻�վֱ�����ڵ����ǣ����޸������ѹ滮����·����������ͻ
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
						route[x][j + 1] = -1;//ֱ�ӵ���Ϊֹ���Ѻ�·����
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
//���л�վ���¹滮��cmp_flag��ʾʹ����һ���������
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
int bfs_with_target2(int i, int sat_id)//Ѱ��һ���ӻ�վi������sat_id��(�޳�ͻ)·����������ans[]�У�����ans[0]==sat_id��ans[ansp-1]Ϊbst_id(����)��������ansp��ʧ���򷵻�-1
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
			//��·����ͻ�ı�ֱ�Ӳ���

			if (visited[G[v.id][j].id] == 0)
			{
				if (v.dis + G[v.id][j].dis > D)continue;
				if (G[v.id][j].id == sat_id)//�ɹ�������Ŀ�꣬�������������������
				{
					flag = 1;
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					real_dis[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 3)//����Ŀ�����ǵĽ������ǣ�������·������
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
	vector<int>alternative_sat;//�ڻ�վi����bfs�������ҵ��ļ����ʺ�����Ϊ�������ǵ�����id
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
				if (v.dis + G[v.id][j].dis > D)//��������ƾ����ڣ��޷�����G[v.id][j].id
				{
					continue;
				}
				int flag = 0; int lost_bst_id = -1;
				if (type2[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type2[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					visited[G[v.id][j].id] = 1;
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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
				if (type2[G[v.id][j].id] == 3)//G[v.id][j].id�Ѿ���ȷ����Ϊ�������ǣ�ֱ�����뱸ѡ��ֹͣ������֧������
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
				if (type2[G[v.id][j].id] == 2)//����Ѿ�ȷ��Ϊ��ת���ǣ��򲻿������뱸ѡ����������������֧��������
				{
					father_id[G[v.id][j].id] = v.id;
					Node a(G[v.id][j].id, v.dis + G[v.id][j].dis);
					q.push(a);
					real_dis_to_sat[G[v.id][j].id] = v.dis + G[v.id][j].dis;
					continue;
				}
				if (type2[G[v.id][j].id] == 1)//�����δ���Ź����͵����ǣ����뱸ѡ����������������֧����
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
			if (target2 != -1 && target2 != ans[0])//�Ѿ��л�վ�����������ߣ��ҽ������ǲ�һ��
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

		type2[ans[0]] = 3;//ȷ�������������

		for (int w = ansp - 2; w >= 1; w--)//ȷ����;����Ϊ��ת�������
		{
			type2[ans[w]] = 2;
		}
		for (int w = ansp - 1; w >= 1; w--)//��·����ÿ���ߴ��ϱ�ǣ��������ǵ�id
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
	if (check == 0)//������������ѡ���ж��Ҳ�������Ϊ�������ǵģ������·�϶������˳�ͻ��
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
		type2[closest_sat] = 3;//��Ŀû�б�֤һ����վֻ������һ������
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
						route2[x][j + 1] = -1;//ֱ�ӵ���Ϊֹ���Ѻ�·����
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
	if (D > 475)D = 475; //��·����������D����ʱ���൱�ڼ���û��·������Լ���������´��书�Ĺ����ܳɱ�����
	for (int i = 0; i < N; i++)
	{
		cin >> type[i];
		if (type[i] == 1) //�������н�����ݣ�0Ϊ��վ��1Ϊ���ǣ���δ�ֻ�Ϊ����/��ת���ǣ�
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
	//��ͼ���ڽӱ�
	for (int i = 0; i < E; i++)
	{
		cin >> u >> v >> dis;
		Node a(u, dis);
		Node b(v, dis);
		G[u].push_back(b);
		G[v].push_back(a);
	}
	for (int i = 0; i < N; i++) //���ھ����򣬶Խ��������Ӱ��
	{
		sort(G[i].begin(), G[i].end(), cmp);
	}
	//��ʼʱ�����л�վ��û���ҵ���
	memset(already_has_home, 0, sizeof(already_has_home));

	//��ÿ����վΪԴ�����bfs�������ܵ�������Ǵ������Լ���id�Լ����룬����¼�����վ�ܵ������������
	all_bst_bfs();

	//ȷ����վ�Ŀ���˳�򣬲���˳��Ϊÿ����վ�ҵ����ʵĽ������ǣ�������·����ͻԼ����
	search_all();
	
	for (int i = 0; i < 1; i++)
	{
		memset(already_research, 0, sizeof(already_research));
		//���õ�һ�ι滮����Ϣ�������л�վ���¹滮һ�Σ���֤����·������ͻ��������ѡ���һ�ι滮�Ľ�������
		research_all(2);
	}

	//�����
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


