/*********************************************
 * OPL 12.9.0.0 Model
 * Author: banian
 * Creation Date: 2024��7��15�� at ����9:42:56
 *********************************************/
int n = 6;//������
range jobs = 0..n;
int m = 2;//��ˮ���������
int s = 2;//��������׶���(�������)
int F = 2;//��ˮ���乤����
int L0=1;int L1=2;int L2=3;//�������׶λ�������
int L=3;//ÿ���׶ζ�����̨����������ȫ��ͬ
range factories = 1..F;
range stages = 1..m;
float beta2[stages][1..L]=[[6,8,0],[7,6,5]];
float gamma2=1;
float theta2=0.5;
float beta1[1..m]=[6,7];
float gamma1[1..m]=[1,1.2];
float theta1[1..m]=[0.5,0.7];
float t[1..2]=[2,3];//ת��ʱ��
float t1=2;
float t2=3;
float mu=3;//ת���ܺ�ϵ��
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
// ׼��ʱ��ֻ��׶��й�(�ͻ����޹�)���������ĸ��������ĸ��׶�ֻҪ�׶���ͬ��׼��ʱ�����ͬ
float ST2[0..n][0..n][1..s] = [[[0,0],[1,2],[1,2],[2,0],[2,3],[1,2],[2,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[1,1]],
                              [[0,0],[1,2],[0,0],[2,0],[2,1],[1,1],[1,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[2,1]],
                              [[0,0],[1,2],[2,2],[1,0],[0,0],[2,2],[1,2]],
                              [[0,0],[1,1],[1,2],[2,0],[1,1],[0,0],[1,2]],
                              [[0,0],[2,1],[2,1],[2,0],[2,1],[1,1],[0,0]]];
float v[stages][1..3]=[[1,1.2,1],[1.2,1,1]];
int Z1[1..2][1..2]=[[1,3],[2,6]];//��Զ�������
int Z2[1..2]=[2,3];//��Թ��򼯺�
dvar float T1;//��������
dvar float T2;//��������
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
dvar float Cmax;//����깤ʱ��
dvar boolean X[jobs][jobs]; 
dvar boolean Y[0..n][1..L][0..s];//����j�����ڽ׶Ρ�����
dvar boolean Z[0..n][0..n][1..L][0..s];//ͬһ̨�����Ϲ�����Ⱥ�˳��
dvar float D[1..n][0..m];
dvar float d[0..n][0..m];//�깤ʱ��
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
	// ��ͷ����Ŀ=��β����Ŀ=��������F�������У�����������ĿF=1ʱ������������ֻ��һ�����С�
	// Constraint 4,5
	F == sum(j in 1..n) X[j][0]; 	
	F == sum(j in 1..n) X[0][j]; 
	// ���ӻ�Լ�� Constraint 6
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
  //forall(j in 1..n,f in 1..F, k in 1..m) sum(i in 1..L) Y[j][i][f][k] == X[j][f];//���⹤��ֻ���ڲ�ͬ�׶ε�����һ�������ϳ��� 
	forall(j in 1..n) sum(l in 1..L1) Y[j][l][1] == 1;
	forall(j in 1..n) sum(l in 1..L2) Y[j][l][2] == 1;
  //Constraint 10 ���⹤�����������н׶�(��������׶�)�����л�����
    forall(l in 1..L1) Y[0][l][1]==1;
	forall(l in 1..L2) Y[0][l][2]==1;
  	//Constraint 11 
  	//ֻ��һ��ǰ����ֻ��һ�����
	//�������j1����������̨�����ϣ�����j1Ϊǰ���Ĺ�������û��
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j1][l][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j1][l][2];
	//Constraint 12 �������j2����������̨�����ϣ�����j2Ϊ��̵Ĺ�������û��
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j2][l][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][2]<=Y[j2][l][2];
	//Constraint 13 ���ӻ�Լ��
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j2][l][1]; 
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j2][l][2];
    //Constraint 14 ���ӻ�Լ��
    forall(j1 in 0..n, l in 1..L1) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][1];
    forall(j1 in 0..n, l in 1..L2) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][2];
	//Constraint 15 ���ӻ�Լ�� 
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L1) w2-w1+100*Z[j1][j2][l][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L2) w2-w1+100*Z[j1][j2][l][2]<=100-1;
    //Constraint 16 �����ڵڶ��׶εĿ�ʼʱ��
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
	//Constraint 25 ǰ�����ڵ�ǰ�׶��У�����ͬһ̨����
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