/*********************************************
 * OPL 12.9.0.0 Model
 * Author: banian
 * Creation Date: January 17, 2025 at 3:21:41 PM
 *********************************************/
int n = 6;//Number of orders (jobs).
range jobs = 0..n;
int m = 2;//Number of flow shop machines (Phase 1).
int s = 2;//Number of stages in hybrid flow shop (Phase 2).
int F = 2;//Number of flow shop factories(Phase 1).
int L0=1;int L1=2;int L2=3;//Number of machines at different stage on Phase 2.
int L=3;
range factories = 1..F;
range stages = 1..m;
float beta2[stages][1..L]=[[6,8,0],[7,6,5]];
float gamma2=1;
float theta2=0.5;
float beta1[1..m]=[6,7];
float gamma1[1..m]=[1,1];
float theta1[1..m]=[0.5,0.7];
float t[1..2]=[1,2];//Transportation time.
float t1=1;
float t2=2;
float mu=3;//Energy consumption factor on transportation phase.
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
// The preparation time is only related to the stage (not to the machine)
float ST2[0..n][0..n][1..s] = [[[0,0],[1,2],[1,2],[2,0],[2,3],[1,2],[0,1]],
                              [[0,0],[0,0],[2,2],[2,0],[1,1],[2,1],[0,1]],
                              [[0,0],[1,2],[0,0],[2,0],[2,1],[1,1],[0,1]],
                              [[0,0],[1,1],[2,2],[0,0],[1,1],[1,2],[0,1]],
                              [[0,0],[1,2],[2,2],[1,0],[0,0],[2,2],[0,2]],
                              [[0,0],[1,1],[1,2],[2,0],[1,1],[0,0],[0,2]],
                              [[0,0],[2,1],[2,1],[2,0],[2,1],[1,1],[0,0]]];
float v[stages][1..3]=[[1,1.2,1],[1.2,1,1]];
//float v[stages][1..3]=[[1,1,1],[1,1,1]];
int Z1[1..2][1..2]=[[1,3],[2,6]];//Mating Order Sets
int Z2[1..2]=[2,3];//Mating Operation Sets
dvar float T1;//Auxiliary variable
dvar float T2;//Auxiliary variable
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
dvar float Cmax;//Makespan
dvar boolean X[0..n][1..F]; //Phase 1 
dvar boolean ZZ[0..n][0..n][1..F]; //Sequencing of jobs in the same factory.
dvar boolean Y[0..n][1..L][0..s];//J is allocated on the machine of the stage.
dvar boolean Z[0..n][0..n][1..L][0..s];//Sequencing of jobs in the same machine on Phase 2.
dvar float D[0..n][0..m];
dvar float d[0..n][0..s];
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
	// Constraint 2 Virtual jobs must be assigned in all factories.
    forall(f in 1..F) X[0][f] == 1; 
    // Constraint 3
    forall(j in 1..n) sum(f in 1..F) X[j][f] == 1;
    // Constraint 4 only one precursor and only one successor.
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,f in 1..F) ZZ[j1][j2][f]<=X[j1][f];
	// Constraint 5
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,f in 1..F) ZZ[j1][j2][f]<=X[j2][f];
	// Constraint 6,7,8 No subring constraint.
	forall(j2 in 0..n, f in 1..F) sum(j1 in 0..n: j1!=j2) ZZ[j1][j2][f] == X[j2][f]; 
	forall(j1 in 0..n, f in 1..F) sum(j2 in 0..n: j1!=j2) ZZ[j1][j2][f] == X[j1][f];
	forall(j1 in 1..n,j2 in 1..n:j1!=j2, f in 1..F) u2-u1+100*ZZ[j1][j2][f]<=100-1;
	// Constraint 9
	forall(j in 0..n, i in 0..m) D[j][i] >=0;
	// Constraint 10
	forall(j in 1..n, i in 1..m) D[j][i] >= D[j][i-1] + P1[j][i];
	// Constraint 11
	forall(j1 in 1..n, j2 in 1..n :j1!=j2, i in 1..m,f in 1..F)  D[j2][i] >= D[j1][i] + P1[j2][i] + ST1[j1][j2][i] + (ZZ[j1][j2][f] -1) * h1;
	// Constraint 
	forall(j in 1..n)  D[j][m] == D[j][m-1] + P1[j][m];
	// Constraint 12
	forall(j in 1..n, i in 1..m,f in 1..F) D[j][i] >= ST1[0][j][i] + P1[j][i] + (ZZ[0][j][f]-1)*h1;
	// Constraint 13
	forall(j in 1..n) sum(l in 1..L1) Y[j][l][1] == 1;
	forall(j in 1..n) sum(l in 1..L2) Y[j][l][2] == 1;
    //Constraint 14 Virtual jobs are assigned to all machines in all phases (including virtual phases)
    forall(l in 1..L1) Y[0][l][1]==1;
	forall(l in 1..L2) Y[0][l][2]==1;
	//Constraint 
	sum(l in 1..L1) Z[2][6][l][1]==1;
	sum(l in 1..L2) Z[1][3][l][2]==1;
	//Constraint 15,16 only one precursor and only one successor
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j1][l][1];
	forall(j1 in 1..n, j2 in 0..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j1][l][2];
	//Constraint 15,16 only one precursor and only one successor
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L1) Z[j1][j2][l][1]<=Y[j2][l][1];
	forall(j1 in 0..n, j2 in 1..n:j1!=j2,l in 1..L2) Z[j1][j2][l][2]<=Y[j2][l][2];
	//Constraint 17,18,19 No subring constraint.
    forall(j2 in 0..n, l in 1..L1) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j2][l][1]; 
    forall(j2 in 0..n, l in 1..L2) sum(j1 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j2][l][2];
    //Constraint 17,18,19 No subring constraint.
    forall(j1 in 0..n, l in 1..L1) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][1] == Y[j1][l][1];
    forall(j1 in 0..n, l in 1..L2) sum(j2 in 0..n: j1!=j2) Z[j1][j2][l][2] == Y[j1][l][2];
	//Constraint 17,18,19 No subring constraint.
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L1) w2-w1+100*Z[j1][j2][l][1]<=100-1;
    forall(j1 in 1..n,j2 in 1..n:j1!=j2, l in 1..L2) w2-w1+100*Z[j1][j2][l][2]<=100-1;
    //Constraint 20 
    forall(j in 0..n,k in 0..s) d[j][k]>=0;
    //Constraint 21 Start time of the job on Phase 2.
	forall(j in 1..n) d[j][0]>=D[j][m]+t1+(Y[j][1][1]-1)*h2;
	forall(j in 1..n) d[j][0]>=D[j][m]+t2+(Y[j][2][1]-1)*h2;
    //Constraint 22
    forall(j in 1..n, l in 1..L1) d[j][1]>=d[j][0]+P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n, l in 1..L2) d[j][2]>=d[j][1]+P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;	 	
    //Constraint 23
	forall(l in 1..L1) T1>=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(Y[2][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(Y[1][l][2]-1)*h2;
	//Constraint 23
	forall(l in 1..L1) T1>=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(Y[6][l][1]-1)*h2;
	forall(l in 1..L2) T2>=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(Y[3][l][2]-1)*h2;
	//Constraint 24
	forall(l in 1..L1) T1<=d[2][0]+P2[2][1]/v[1][l]+P2[6][1]/v[1][l]+(1-Y[2][l][1])*h2+M*(1-u5);
	forall(l in 1..L2) T2<=d[1][1]+P2[1][2]/v[2][l]+P2[3][2]/v[2][l]+(1-Y[1][l][2])*h2+M*(1-u7);
	//Constraint 24 
	forall(l in 1..L1) T1<=d[6][0]+P2[6][1]/v[1][l]+P2[2][1]/v[1][l]+(1-Y[6][l][1])*h2+M*(1-u6);
    forall(l in 1..L2) T1<=d[3][1]+P2[3][2]/v[2][l]+P2[1][2]/v[2][l]+(1-Y[3][l][2])*h2+M*(1-u8);
    //Constraint 25
    u5+u6>=1;
    u7+u8>=1;
    //Constraint 26
    d[2][1]>=T1;
	d[1][2]>=T2;
	//Constraint 27
	d[6][1]>=T1;
	d[3][2]>=T2;
	//Constraint 28 
 	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L1) d[j2][1]>=d[j1][1]+P2[j2][1]/v[1][l]+ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 1..n, j2 in 1..n :j1!=j2,l in 1..L2) d[j2][2]>=d[j1][2]+P2[j2][2]/v[2][l]+ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
	//Constraint 
	forall(j in 0..n,f in 1..F, i in 1..m) PEC1[j][f][i] >=0;
    forall(j in 0..n,f in 1..F, i in 1..m) SEC1[j][f][i]>=0;
    forall(j in 0..n,f in 1..F, i in 1..m) IEC1[j][f][i]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) PEC2[j][l][k]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) SEC2[j][l][k]>=0;
    forall(j in 0..n,l in 1..L,k in 1..s) IEC2[j][l][k]>=0;
    //Constraint 29
	forall(j in 1..n,f in 1..F, i in 1..m) PEC1[j][f][i] >= P1[j][i]*beta1[i]+(X[j][f]-1)*h1;
	//Constraint 30
	forall(j1 in 0..n,j2 in 1..n,f in 1..F, i in 1..m) SEC1[j1][f][i] >= ST1[j1][j2][i]*gamma1[i]+(ZZ[j1][j2][f]-1)*h1;
	//Constraint 31
	forall(j1 in 0..n,j2 in 1..n,f in 1..F, i in 2..m) IEC1[j1][f][i] >= theta1[i]*(D[j2][i-1]-D[j1][i]-ST1[j1][j2][i])+(ZZ[j1][j2][f]-1)*h1;
    //Constraint 32
	forall(j in 1..n,l in 1..L1) PEC2[j][l][1]>=beta2[1][l]*P2[j][1]/v[1][l]+(Y[j][l][1]-1)*h2;
	forall(j in 1..n,l in 1..L2) PEC2[j][l][2]>=beta2[2][l]*P2[j][2]/v[2][l]+(Y[j][l][2]-1)*h2;
    //Constraint 33
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) SEC2[j1][l][1]>=gamma2*ST2[j1][j2][1]+(Z[j1][j2][l][1]-1)*h2;
	forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) SEC2[j1][l][2]>=gamma2*ST2[j1][j2][2]+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 34
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L1) IEC2[j1][l][1]>=theta2*(d[j2][0]-d[j1][1]-ST2[j1][j2][1])+(Z[j1][j2][l][1]-1)*h2; 
    forall(j1 in 0..n,j2 in 1..n:j1!=j2,l in 1..L2) IEC2[j1][l][2]>=theta2*(d[j2][1]-d[j1][2]-ST2[j1][j2][2])+(Z[j1][j2][l][2]-1)*h2;
    //Constraint 
    TE2>=0;
    TE1>=0;
    TE2 >= sum(k in 1..s,l in 1..L,j in 0..n) (PEC2[j][l][k]+SEC2[j][l][k]+IEC2[j][l][k]);
    TE1 >= sum(f in 1..F,i in 1..m,j in 0..n) (PEC1[j][f][i]+SEC1[j][f][i]+IEC1[j][f][i]);
	forall(j in 1..n,l in 1..L1) REC[j][l] >=0;
	//Constraint 35
	forall(j in 1..n,l in 1..L1) REC[j][l] >= mu*t[l]+(Y[j][l][1]-1)*h2;
	TE3 >= sum(j in 1..n,l in 1..L1) REC[j][l]; 
	//Constraint 36
	TEC >= TE1+TE2+TE3;
	//TEC <=397;
	// Constraint 37
	forall(j in 1..n) Cmax >= d[j][s];
	//Cmax<=20;
}