param n;
set Q := 1..n by 1;
set S{1..n};
set Y = S[1] cross S[2] cross S[3];

set Y1 = setof{(d1,d2,d3) in Y} (d2,d3);
set Y2 = setof{(d1,d2,d3) in Y} (d1,d3);
set Y3 = setof{(d1,d2,d3) in Y} (d1,d2);

param A{i in 1..n, (d1,d2,d3) in Y};

var x{i in 1..n, j in S[i]} >= 0,<=1;

var p{i in 1..n};

maximize fl: 0;

s.t. I11 {k in S[1]}: sum{(d1,d2) in Y1} (x[2,d1]*x[3,d2]*A[1,k,d1,d2]) <= p[1];
s.t. I12 {k in S[2]}: sum{(d1,d2) in Y2} (x[1,d1]*x[3,d2]*A[2,d1,k,d2]) <= p[2];
s.t. I13 {k in S[3]}: sum{(d1,d2) in Y3} (x[1,d1]*x[2,d2]*A[3,d1,d2,k]) <= p[3];
s.t. I3 {i in 1..n}: sum{j in S[i]} x[i,j] = 1;
s.t. I5: (sum{(k1,k2,k3) in Y} (x[1,k1]*x[2,k2]*x[3,k3]*(A[1,k1,k2,k3]+A[2,k1,k2,k3]+A[3,k1,k2,k3])) - (sum{i in Q} p[i])) >= 0;