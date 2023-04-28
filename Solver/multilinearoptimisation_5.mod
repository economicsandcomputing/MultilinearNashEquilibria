param n;
set Q := 1..n by 1;
set S{1..n};
set Y = S[1] cross S[2] cross S[3] cross S[4] cross S[5];

set Y1 = setof{(d1,d2,d3,d4,d5) in Y} (d2,d3,d4,d5);
set Y2 = setof{(d1,d2,d3,d4,d5) in Y} (d1,d3,d4,d5);
set Y3 = setof{(d1,d2,d3,d4,d5) in Y} (d1,d2,d4,d5);
set Y4 = setof{(d1,d2,d3,d4,d5) in Y} (d1,d2,d3,d5);
set Y5 = setof{(d1,d2,d3,d4,d5) in Y} (d1,d2,d3,d4);

param A{i in 1..n, (d1,d2,d3,d4,d5) in Y};

var x{i in 1..n, j in S[i]} >= 0,<=1;

var p{i in 1..n};

maximize fl: sum{(k1,k2,k3,k4,k5) in Y} (x[1,k1]*x[2,k2]*x[3,k3]*x[4,k4]*x[5,k5]*(sum{i in Q} A[i,k1,k2,k3,k4,k5])) - (sum{i in Q} p[i]);

s.t. I11 {k in S[1]}: sum{(d1,d2,d3,d4) in Y1} (x[2,d1]*x[3,d2]*x[4,d3]*x[5,d4]*A[1,k,d1,d2,d3,d4]) <= p[1];
s.t. I12 {k in S[2]}: sum{(d1,d2,d3,d4) in Y2} (x[1,d1]*x[3,d2]*x[4,d3]*x[5,d4]*A[2,d1,k,d2,d3,d4]) <= p[2];
s.t. I13 {k in S[3]}: sum{(d1,d2,d3,d4) in Y3} (x[1,d1]*x[2,d2]*x[4,d3]*x[5,d4]*A[3,d1,d2,k,d3,d4]) <= p[3];
s.t. I14 {k in S[4]}: sum{(d1,d2,d3,d4) in Y4} (x[1,d1]*x[2,d2]*x[3,d3]*x[5,d4]*A[4,d1,d2,d3,k,d4]) <= p[4];
s.t. I15 {k in S[5]}: sum{(d1,d2,d3,d4) in Y5} (x[1,d1]*x[2,d2]*x[3,d3]*x[4,d4]*A[5,d1,d2,d3,d4,k]) <= p[5];
s.t. I3 {i in 1..n}: sum{j in S[i]} x[i,j] = 1;
	