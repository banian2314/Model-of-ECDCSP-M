/*********************************************
 * OPL 12.9.0.0 Model
 * Author: banian
 * Creation Date: 2024年7月15日 at 下午9:42:56
 *********************************************/
int n = 6;//订单数
range jobs = 0..n;
int m = 2;//流水车间机器数
int s = 2;//混流车间阶段数(最大工序数)
int F = 2;//流水车间工厂数
int L0=1;int L1=2;int L2=3;//工厂各阶段机器数量
int L=3;//每个阶段都有两台机器，且完全相同
range factories = 1..F;
range stages = 1..m;
float beta2[stages][1..L]=[[6,8,0],[7,6,5]];
float gamma2=1;
float theta2=0.5;
float beta1[1..m]=[6,7];
float gamma1[1..m]=[1,1.2];
float theta1[1..m]=[0.5,0.7];
float t[1..2]=[2,3];//转移时间
float t1=2;
float t2=3;
float mu=3;//转移能耗系数
float h1 = 100000;
float h2 = 1000;
float M = 10000;
float P1[0..n][1..m] = [[0,0],[3,2],[2,2],[3,3],[3,2],[2,2],[3,2]];             
float P2[0..n][1..s] = [[0,0],[3,3.6],[2.4,2],[3.6,0],[3.6,3.6],[2.4,2],[3.6,2]];
float ST1[0..n][0..n][1..m] = [[[0,0],[1,2],[1,2],[2,0],[2,3],[1,2],[2,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[1,1]],
                              [[0,0],[1,2],[0,0],[2,0],[2,1],[1,1],[1,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[2,1]],
                              [[0,0],[1,2],[2,2],[1,0],[0,0],[2,2],[1,2]],
                              [[0,0],[1,1],[1,2],[2,0],[1,1],[0,0],[1,2]],
                              [[0,0],[2,1],[2,1],[2,0],[2,1],[1,1],[0,0]]];
// 准备时间只与阶段有关(和机器无关)，不管在哪个工厂的哪个阶段只要阶段相同，准备时间便相同
float ST2[0..n][0..n][1..s] = [[[0,0],[1,2],[1,2],[2,0],[2,3],[1,2],[2,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[1,1]],
                              [[0,0],[1,2],[0,0],[2,0],[2,1],[1,1],[1,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[2,1]],
                              [[0,0],[1,2],[2,2],[1,0],[0,0],[2,2],[1,2]],
                              [[0,0],[1,1],[1,2],[2,0],[1,1],[0,0],[1,2]],
                              [[0,0],[2,1],[2,1],[2,0],[2,1],[1,1],[0,0]]];
float v[stages][1..3]=[[1,1.2,1],[1.2,1,1]];
int Z1[1..2][1..2]=[[1,3],[2,6]];//配对订单集合
int Z2[1..2]=[2,3];//配对工序集合
dvar float T1;//辅助变量
dvar float T2;//辅助变量
dvar boolean u1;
dvar boolean u2;
dvar boolean u3;
dvar boolean u4;
dvar boolean u5;
dvar boolean u6;
dvar boolean u7;
dvar boolean u8;
int w1=400;
int w2=300;
dvar float Cmax;//最大完工时间
dvar boolean X[jobs][jobs]; 
dvar boolean Y[0..n][1..L][0..s];//工件j分配在阶段、机器
dvar boolean Z[0..n][0..n][1..L][0..s];//同一台机器上工序的先后顺序
dvar float D[1..n][0..m];
dvar float d[0..n][0..m];//完工时间
dvar float TEC;
dvar float TE;
dvar float PEC2[0..n][1..L][1..m];
dvar float SEC2[0..n][1..L][1..m];
dvar float IEC2[0..n][1..L][1..m];
dvar float PEC1;
dvar float SEC1;
dvar float IEC1;
dvar float REC;
//dvar float PEC2;
//dvar float SEC2;
//dvar float IEC2;
execute PARAMS {cplex.tilim = 1;cplex.threads = 3;}
//minimize staticLex(Cmax,TEC);
minimize Cmax;
subject to{
	// Constraint 2,3
	forall(j2 in 1..n) sum(j1 in 0..n: j1!=j2) X[j1][j2] == 1; 
	forall(j1 in 1..n) sum(j2 in 0..n: j1!=j2) X[j1][j2] == 1; 
	//forall(j1 in 1..n, j2 in 1..n-1 :j2>j1) X[j1][j2]+X[j2][j1]<=1;
	// “头”数目=“尾”数目=工厂数（F个子序列），当工厂数目F=1时，代表单工厂，只有一个序列。
	// Constraint 4,5
	F == sum(j in 1..n) X[j][0]; 	
	F == sum(j in 1..n) X[0][j]; 
	// 无子环约束 Constraint 6
	forall(j1 in 1..n, j2 in 1..n :j1!=j2) w2-w1+(n-1)*X[j1][j2] <= n-2;
	// Constraint 7
	forall(j in 1..n, i in 1..m) D[j][i] >= D[j][i-1] + P1[j][i];
	// Constraint 8
	forall(j1 in 1..n, j2 in 1..n :j1!=j2, i in 1..m)  D[j2][i] >= D[j1][i] + P1[j2][i] + ST1[j1][j2][i] + (X[j1][j2] -1) * h1;
	forall(j in 1..n)  D[j][m] == D[j][m-1] + P1[j][m];
	forall(j in 1..n, i in 1..m) D[j][i] >= ST1[0][j][i] + P1[j][i] + (X[0][j]-1)*h1;
	forall(j in 1..n, i in 1..m-1) D[j][i] >= ST1[0][j][i+1] + (X[0][j] -1) * h1;
	// Constraint 9
	//forall(j in 1..n, i in 1..m) D[j][i] >= STS[j][i] + P[j][i] + (X[0][j] -1) * h;
   	// Constraint 9
  //forall(j in 1..n,f in 1..F, k in 1..m) sum(i in 1..L) Y[j][i][f][k] == X[j][f];//任意工件只能在不同阶段的其中一个机器上出现 
	forall(j in 1..n) sum(l in 1..L1) Y[j][l][1] == 1;
	forall(j in 1..n) sum(l in 1..L2) Y[j][l][2] == 1;
  //Constraint 10 虚拟工件分配在所有阶段(包括虚拟阶段)的所有机器上
    forall(l in 1..L1) Y[0][l][1]==1;
	forall(l in 1..L2) Y[0][l][2]==1;
  	//Constraint 11 
  	//只有一个前驱，只有一个后继
	//如果工件j1不出现在这台机器上，则以j1为前驱的工件绝对没有
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j1][l][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j1][l][2];
	//Constraint 12 如果工件j2不出现在这台机器上，则以j2为后继的工件绝对没有
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j2][l][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][2]<=Y[j2][l][2];
	//Constraint 13 无子环约束
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j2][l][1]; 
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j2][l][2];
    //Constraint 14 无子环约束
    forall(j1 in 0..n, l in 1..L1) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][1];
    forall(j1 in 0..n, l in 1..L2) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][2];
	//Constraint 15 无子环约束 
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L1) w2-w1+100*Z[j1][j2][l][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L2) w2-w1+100*Z[j1][j2][l][2]<=100-1;
    //Constraint 16 工件在第二阶段的开始时间
	forall(j in 1..n) d[j][0]>=D[j][m]+t1+(Y[j][1][1]-1)*h2;
	forall(j in 1..n) d[j][0]>=D[j][m]+t2+(Y[j][2][1]-1)*h2;
    //forall(k in 0..m) d[0][k]==0;
    //Constraint 17
    forall(j in 1..n, l in 1..L1) d[j][1]>=d[j][0]+P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n, l in 1..L2) d[j][2]>=d[j][1]+P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;	 	
    //Constraint 18
	forall(l in 1..L1) T1>=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(Y[2][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(Y[1][l][2]-1)*h2;
	//Constraint 19
	forall(l in 1..L1) T1>=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(Y[6][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(Y[3][l][2]-1)*h2;
	//Constraint 20
	forall(l in 1..L1) T1<=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(1-Y[2][l][1])*h2+M*(1-u5);
	forall(l in 1..L2) T2<=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(1-Y[1][l][2])*h2+M*(1-u7);
	//Constraint 21 
	forall(l in 1..L1) T1<=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(1-Y[6][l][1])*h2+M*(1-u6);
    forall(l in 1..L2) T1<=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(1-Y[3][l][2])*h2+M*(1-u8);
    //Constraint 22
    u5+u6>=1;
    u7+u8>=1;
    //Constraint 23
    d[2][1]>=T1;
	d[1][2]>=T2;
	//Constraint 24
	d[6][1]>=T1;
	d[3][2]>=T2;
	//Constraint 25 前提是在当前阶段中，共用同一台机器
 	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L1) d[j2][1]>=d[j1][1]+P2[j2][1]/v[1][l]+ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L2) d[j2][2]>=d[j1][2]+P2[j2][2]/v[2][l]+ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
	//Constraint 26
	//PEC1 >= sum(j in 1..n,i in 1..m) P2[j][i]*beta1[i];
	//Constraint 27
	//SEC1 >= sum(j1 in 0..n, j2 in 1..n :j1!=j2,i in 1..m) X[j1][j2]*gamma1[i]*ST1[j1][j2][i];
	//Constraint 28
	//IEC1 >= sum(j1 in 0..n, j2 in 1..n :j1!=j2,i in 2..m) theta1[i]*X[j1][j2]*(D[j2][i-1]-D[j2][i]-ST1[j1][j2][i]);
	//Constraint 29
	forall(j in 1..n,l in 1..L1) PEC2[j][l][1]>=beta2[1][l]*P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n,l in 1..L2) PEC2[j][l][2]>=beta2[2][l]*P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;
    //Constraint 30
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) SEC2[j2][l][1]>=gamma2*ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) SEC2[j2][l][2]>=gamma2*ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 31
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) IEC2[j1][l][1]>=theta2*(d[j2][0]-d[j1][1]-ST2[j1][j2][1])+(Z[j1][j2][l][1]-1)*h2; 
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) IEC2[j1][l][2]>=theta2*(d[j2][1]-d[j1][2]-ST2[j1][j2][2])+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 
    TE >= sum(k in 1..s,l in 1..L,j in 0..n) (PEC2[j][l][k]+SEC2[j][l][k]+IEC2[j][l][k]);
	//Constraint 32
	REC >=0;
	REC >= mu*sum(j in 1..n,l in 1..2) (t[l]+(Y[j][l][1]-1)*h2);
	//Constraint 33
	//TEC >= PEC1+SEC1+IEC1+TE+REC;
	TEC >= TE+REC;
	// Constraint 23
	forall(j in 1..n) Cmax >= d[j][s];
}