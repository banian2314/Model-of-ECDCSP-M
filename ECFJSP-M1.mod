/*********************************************
 * OPL 12.9.0.0 Model
 * Author: banian
 * Creation Date: 2024年7月17日 at 下午4:29:48
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
float gamma1[1..m]=[1,1];
float theta1[1..m]=[0.5,0.7];
float t[1..2]=[1,2];//转移时间
float t1=1;
float t2=2;
float mu=3;//转移能耗系数
float h1 = 100000;
float h2 = 1000;
float M = 10000;
float P1[0..n][1..m] = [[0,0],[3,2],[2,2],[3,3],[3,2],[2,2],[3,2]];             
//float P2[0..n][1..s] = [[0,0],[3,3.6],[2.4,2],[3.6,0],[3.6,3.6],[2.4,2],[0,2]];
float P2[0..n][1..s] = [[0,0],[3,3.6],[2.4,2],[3.6,0],[3.6,3.6],[2.4,2],[0,2]];
//float P2[0..n][1..s] = [[0,0],[3,3],[2,2],[3,0],[3,3],[2,2],[0,2]];
float ST1[0..n][0..n][1..m] = [[[0,0],[1,2],[1,2],[2,1],[2,3],[1,2],[2,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[1,1]],
                              [[0,0],[1,2],[0,0],[2,1],[2,1],[1,1],[1,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[2,1]],
                              [[0,0],[1,2],[2,2],[1,1],[0,0],[2,2],[1,2]],
                              [[0,0],[1,1],[1,2],[2,2],[1,1],[0,0],[1,2]],
                              [[0,0],[2,1],[2,1],[2,1],[2,1],[1,1],[0,0]]];
// 准备时间只与阶段有关(和机器无关)，不管在哪个工厂的哪个阶段只要阶段相同，准备时间便相同
float ST2[0..n][0..n][1..s] = [[[0,0],[1,2],[1,2],[2,0],[2,3],[1,2],[0,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[0,1]],
                              [[0,0],[1,2],[0,0],[2,0],[2,1],[1,1],[0,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[0,1]],
                              [[0,0],[1,2],[2,2],[1,0],[0,0],[2,2],[0,2]],
                              [[0,0],[1,1],[1,2],[2,0],[1,1],[0,0],[0,2]],
                              [[0,0],[2,1],[2,1],[2,0],[2,1],[1,1],[0,0]]];
float v[stages][1..3]=[[1,1.2,1],[1.2,1,1]];
//float v[stages][1..3]=[[1,1,1],[1,1,1]];
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
dvar boolean X[0..n][1..F]; //第一阶段
dvar boolean ZZ[0..n][0..n][1..F]; //同一工厂中工序的先后顺序
dvar boolean Y[0..n][1..L][0..s];//工件j分配在阶段、机器
dvar boolean Z[0..n][0..n][1..L][0..s];//同一台机器上工序的先后顺序
dvar float D[0..n][0..m];
dvar float d[0..n][0..s];//完工时间
dvar float TEC;
dvar float TE1;
dvar float TE2;
dvar float TE3;
dvar float PEC2[0..n][1..L][1..s];
dvar float SEC2[0..n][1..L][1..s];
dvar float IEC2[0..n][1..L][1..s];
dvar float PEC1[0..n][1..F][1..m];
dvar float SEC1[0..n][1..F][1..m];
dvar float IEC1[0..n][1..F][1..m];
dvar float REC[1..n][1..L1];
//dvar float PEC2;
//dvar float SEC2;
//dvar float IEC2;
//execute PARAMS {cplex.tilim = 1;cplex.threads = 3;}
//minimize staticLex(TEC,Cmax);
minimize Cmax;
//minimize TEC;
subject to{
	// Constraint 2虚拟工件必须分配在所有工厂中
    forall(f in 1..F) X[0][f] == 1; 
    // Constraint 3
    forall(j in 1..n) sum(f in 1..F) X[j][f] == 1;
    //只有一个前驱，只有一个后继
    //如果工件j1不出现在这个工厂，则以j1为前驱的工件绝对没有
    // Constraint 4
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,f in 1..F) ZZ[j1][j2][f]<=X[j1][f];
	// Constraint 5
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,f in 1..F) ZZ[j1][j2][f]<=X[j2][f];
	// 无子环约束 Constraint 6
	forall(j2 in 0..n, f in 1..F) sum(j1 in 0..n: j1!=j2) ZZ[j1][j2][f] == X[j2][f]; 
	forall(j1 in 0..n, f in 1..F) sum(j2 in 0..n: j1!=j2) ZZ[j1][j2][f] == X[j1][f];
	forall(j1 in 1..n,j2 in 1..n:j1!=j2, f in 1..F) u2-u1+100*ZZ[j1][j2][f]<=100-1;
	// Constraint 7
	forall(j in 0..n, i in 0..m) D[j][i] >=0;
	// Constraint 8
	forall(j in 1..n, i in 1..m) D[j][i] >= D[j][i-1] + P1[j][i];
	// Constraint 9
	forall(j1 in 1..n, j2 in 1..n :j1!=j2, i in 1..m,f in 1..F)  D[j2][i] >= D[j1][i] + P1[j2][i] + ST1[j1][j2][i] + (ZZ[j1][j2][f] -1) * h1;
	// Constraint 
	forall(j in 1..n)  D[j][m] == D[j][m-1] + P1[j][m];
	// Constraint 10
	forall(j in 1..n, i in 1..m,f in 1..F) D[j][i] >= ST1[0][j][i] + P1[j][i] + (ZZ[0][j][f]-1)*h1;
	// Constraint 
	//forall(j in 1..n, i in 1..m-1,f in 1..F) D[j][i] >= ST1[0][j][i+1] + (ZZ[0][j][f] -1) * h1;
	// Constraint 9
	//forall(j in 1..n, i in 1..m) D[j][i] >= STS[j][i] + P[j][i] + (X[0][j] -1) * h;
   	// Constraint 9
  //forall(j in 1..n,f in 1..F, k in 1..m) sum(i in 1..L) Y[j][i][f][k] == X[j][f];//任意工件只能在不同阶段的其中一个机器上出现 
	// Constraint 11
	forall(j in 1..n) sum(l in 1..L1) Y[j][l][1] == 1;
	forall(j in 1..n) sum(l in 1..L2) Y[j][l][2] == 1;
  //Constraint 12 虚拟工件分配在所有阶段(包括虚拟阶段)的所有机器上
    forall(l in 1..L1) Y[0][l][1]==1;
	forall(l in 1..L2) Y[0][l][2]==1;
	// Z[0..n][0..n][1..L][0..s]
	//Constraint 
	sum(l in 1..L1) Z[2][6][l][1]==1;
	sum(l in 1..L2) Z[1][3][l][2]==1;
  	//Constraint 11 
  	//只有一个前驱，只有一个后继
	//如果工件j1不出现在这台机器上，则以j1为前驱的工件绝对没有
	//Constraint 13
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j1][l][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j1][l][2];
	//Constraint 14 如果工件j2不出现在这台机器上，则以j2为后继的工件绝对没有
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j2][l][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j2][l][2];
	//Constraint 15 无子环约束
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j2][l][1]; 
    forall(j2 in 0..n, l in 1..L2) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j2][l][2];
    //Constraint 16 无子环约束
    forall(j1 in 0..n, l in 1..L1) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][1];
    forall(j1 in 0..n, l in 1..L2) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j1][l][2];
	//Constraint 16 无子环约束 
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L1) w2-w1+100*Z[j1][j2][l][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L2) w2-w1+100*Z[j1][j2][l][2]<=100-1;
    //Constraint 17 
    forall(j in 0..n,k in 0..s) d[j][k]>=0;
    //Constraint 18 工件在第二阶段的开始时间
	forall(j in 1..n) d[j][0]>=D[j][m]+t1+(Y[j][1][1]-1)*h2;
	forall(j in 1..n) d[j][0]>=D[j][m]+t2+(Y[j][2][1]-1)*h2;
    //Constraint 19
    forall(j in 1..n, l in 1..L1) d[j][1]>=d[j][0]+P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n, l in 1..L2) d[j][2]>=d[j][1]+P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;	 	
    //Constraint 20
	forall(l in 1..L1) T1>=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(Y[2][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(Y[1][l][2]-1)*h2;
	//Constraint 21
	forall(l in 1..L1) T1>=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(Y[6][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(Y[3][l][2]-1)*h2;
	//Constraint 22
	forall(l in 1..L1) T1<=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(1-Y[2][l][1])*h2+M*(1-u5);
	forall(l in 1..L2) T2<=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(1-Y[1][l][2])*h2+M*(1-u7);
	//Constraint 23 
	forall(l in 1..L1) T1<=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(1-Y[6][l][1])*h2+M*(1-u6);
    forall(l in 1..L2) T1<=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(1-Y[3][l][2])*h2+M*(1-u8);
    //Constraint 24
    u5+u6>=1;
    u7+u8>=1;
    //Constraint 25
    d[2][1]>=T1;
	d[1][2]>=T2;
	//Constraint 26
	d[6][1]>=T1;
	d[3][2]>=T2;
	//Constraint 27 前提是在当前阶段中，共用同一台机器
 	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L1) d[j2][1]>=d[j1][1]+P2[j2][1]/v[1][l]+ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L2) d[j2][2]>=d[j1][2]+P2[j2][2]/v[2][l]+ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
	//Constraint 
	forall(j in 0..n,f in 1..F, i in 1..m) PEC1[j][f][i] >=0;
    forall(j in 0..n,f in 1..F, i in 1..m) SEC1[j][f][i]>=0;
    forall(j in 0..n,f in 1..F, i in 1..m) IEC1[j][f][i]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) PEC2[j][l][k]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) SEC2[j][l][k]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) IEC2[j][l][k]>=0;
    //Constraint 28
	forall(j in 1..n,f in 1..F, i in 1..m) PEC1[j][f][i] >= P1[j][i]*beta1[i]+(X[j][f]-1)*h1;
	//Constraint 29
	forall(j1 in 0..n,j2 in 1..n,f in 1..F, i in 1..m) SEC1[j1][f][i] >= ST1[j1][j2][i]*gamma1[i]+(ZZ[j1][j2][f]-1)*h1;
	//Constraint 30
	forall(j1 in 0..n,j2 in 1..n,f in 1..F, i in 2..m) IEC1[j1][f][i] >= theta1[i]*(D[j2][i-1]-D[j1][i]-ST1[j1][j2][i])+(ZZ[j1][j2][f]-1)*h1;
    //Constraint 31
	forall(j in 1..n,l in 1..L1) PEC2[j][l][1]>=beta2[1][l]*P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n,l in 1..L2) PEC2[j][l][2]>=beta2[2][l]*P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;
    //Constraint 32
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) SEC2[j1][l][1]>=gamma2*ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) SEC2[j1][l][2]>=gamma2*ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 33
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) IEC2[j1][l][1]>=theta2*(d[j2][0]-d[j1][1]-ST2[j1][j2][1])+(Z[j1][j2][l][1]-1)*h2; 
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) IEC2[j1][l][2]>=theta2*(d[j2][1]-d[j1][2]-ST2[j1][j2][2])+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 
    TE2>=0;
    TE1>=0;
    TE2 >= sum(k in 1..s,l in 1..L,j in 0..n) (PEC2[j][l][k]+SEC2[j][l][k]+IEC2[j][l][k]);
    TE1 >= sum(f in 1..F,i in 1..m,j in 0..n) (PEC1[j][f][i]+SEC1[j][f][i]+IEC1[j][f][i]);
	//Constraint 34
	forall(j in 1..n,l in 1..L1) REC[j][l] >=0;
	forall(j in 1..n,l in 1..L1) REC[j][l] >= mu*t[l]+(Y[j][l][1]-1)*h2;
	TE3 >= sum(j in 1..n,l in 1..L1) REC[j][l]; 
	//Constraint 35
	TEC >= TE1+TE2+TE3;
	//TEC <=397;
	// Constraint 36
	forall(j in 1..n) Cmax >= d[j][s];
	//Cmax<=20;
}