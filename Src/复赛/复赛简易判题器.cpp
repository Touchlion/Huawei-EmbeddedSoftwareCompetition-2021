#include<cstdio>
#include<cstdlib>
#include<iostream>
#include<ctime>
#include<vector>
#include<map>
#include<algorithm>
#include<cmath>
#include<cstring>
#include<iomanip>
#include<queue>
using namespace std;
typedef long long LL;
const LL inf = 1e18;
int N; int E; int C; int D; int PS; int bst_number = 0; int sat_number = 0; int anscount = 0;	int count_sat = 0;
int type[500005];//0表示基站，1表示未决定类型的卫星，2表示中转卫星，3表示接收卫星
int id[500005]; 
int cs[500005]; //基站发射功耗系数
LL total_dis = 0; 
LL transmission_cost = 0; //统计总的传输功耗 
struct Node//邻接点
{
	int id;
	LL dis;
	int target_sat_id = -1;//对每条已经被征用过的边，标记一下此边通向的目标接收卫星。-1表示没有基站征用过这条边
	Node(int ID, LL DIS, int Target_sat_id = -1)
	{
		id = ID; dis = DIS; target_sat_id = Target_sat_id;
	}
	~Node(){}
};
vector<Node>G[600000];//用邻接表实现图
vector<int>route[600000];
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

void set_edge_target(int u, int v, int Target)
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
int the_distance(int from, int to)
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

int main()
{
	freopen("semi_finals_training-2.txt", "r", stdin);
	cin >> N >> E >> C >> D >> PS;
	//cout << N << " " << E << " " << C << " " << D << " " << PS << "\n";
	for (int i = 0; i < N; i++)
	{
		cin >> type[i];
		if (type[i] == 1)
		{
			sat_number++;
		}
		else if (type[i] == 0)
		{
			bst_number++;
		}
	}
	for (int i = 0; i < N; i++)
	{
		cin >> cs[i];
	}
	int u, v; LL dis;
	for (int i = 0; i < E; i++)
	{
		cin >> u >> v >> dis;
		Node a(u, dis);
		Node b(v, dis);
		G[u].push_back(b);
		G[v].push_back(a);
	}
	cin.clear();
	freopen("semi_out.txt", "r", stdin);
	memset(id, 0, sizeof(id));
	int a0, a1; char ch;
	int row = 1;
	while (cin >> a0)
	{
		int flag = 0; int bst_id = a0;
		while (ch = cin.get())
		{
			if (ch == ' '&&isdigit(cin.peek()))
			{
				cin >> a1;
				if (id[a0] == 1)
				{
					cout << "error:接收卫星被设置为中转卫星\n";
					cout << "在第" << row << "行的" << a0 << "号卫星\n";
				}
				route[bst_id].push_back(a1);
				total_dis += the_distance(a0, a1);
				transmission_cost += cs[bst_id] * the_distance(a0, a1);
				a0 = a1; //保持读入的a1前一个结点为a0
			}
			else if (ch == EOF)
			{
				flag = 1; break;
			}
			else 
			{
				if (id[a0] == 0)
				{
					id[a0] = 1; count_sat++;
				}
				row++;
				route[bst_id].push_back(a0);
				route[bst_id].push_back(-1);
				break;
			}

		}
		if (flag)break;
	}

	for (int i = 0; i < N; i++)
	{
		if (type[i] == 0)
		{
			int j = 0;
			for (j = 0; j + 1 < route[i].size() && route[i][j + 1] != -1; j++);
			int sat_id = route[i][j];
			for (int x = 0; x + 1 < route[i].size() && route[i][x + 1] != -1; x++)
			{
				int target = edge_target(route[i][x], route[i][x + 1]);
				if (target != -1 && target != sat_id)
				{
					cout << "规划了冲突的路径，在第" << i << "号基站的" << route[i][x] << "到" << route[i][x + 1] << "链路上，target应为" << target << "，实际sat_id为" << sat_id << "\n";
					for (int w = 0; w < i; w++)
					{
						if (type[w] == 0 && w != i)
						{
							for (int k = 0; k + 1 < route[w].size() && route[w][k + 1] != -1; k++)
							{
								if (route[w][k] == route[i][x] && route[w][k + 1] == route[i][x + 1] || route[w][k + 1] == route[i][x] && route[w][k] == route[i][x + 1])
								{
									int p = 0;
									for (p = 0; p< route[w].size() && route[w][p + 1] != -1; p++);
									if (route[w][p] != sat_id)
									{
										cout << "与第" << w << "号基站的" << route[w][k] << "到" << route[w][k + 1] << "链路冲突\n";
									}
								}
							}
						}
					}
				}
				else
				{
					set_edge_target(route[i][x], route[i][x + 1], sat_id);
				}
			}
		}
	}
	cout << "总共安排了 " << count_sat << " 个接收卫星, 需要站点功耗为" << count_sat*PS << "\n";
	cout << "所有路径长度之和为 " << total_dis << "\n";
	cout << "传输功耗为 " << transmission_cost*C << "\n";
	cout << "总功耗为 " << transmission_cost*C + count_sat*PS << "\n";
}