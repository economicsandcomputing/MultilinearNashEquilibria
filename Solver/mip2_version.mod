param n;
set Q := 1..n by 1;
set S{1..n};
set Y = S[1] cross S[2] cross S[3];

set Y1 = setof{(d1,d2,d3) in Y} (d2,d3);
set Y2 = setof{(d1,d2,d3) in Y} (d1,d3);
set Y3 = setof{(d1,d2,d3) in Y} (d1,d2);

param A{i in 1..n, (d1,d2,d3) in Y};

param U{1..n} >= 0;

var x{i in 1..n, j in S[i]} <=1,>= 0;
var t{1..n};
var r{i in 1..n, j in S[i]} >= 0;
var u{i in 1..n, j in S[i]};
var b{i in 1..n, j in S[i]};
var f{i in 1..n, j in S[i]};

minimize mip2: sum{i in Q, j in S[i]} (f[i,j]-U[i]*b[i,j]);

s.t. I1 {i in Q}: sum {j in S[i]} x[i,j] = 1;
s.t. I21 {j in S[1]}: u[1,j] = sum{(d1,d2) in Y1} (x[2,d1]*x[3,d2]*A[1,j,d1,d2]);
s.t. I22 {j in S[2]}: u[2,j] = sum{(d1,d2) in Y2} (x[1,d1]*x[3,d2]*A[2,d1,j,d2]);
s.t. I23 {j in S[3]}: u[3,j] = sum{(d1,d2) in Y3} (x[1,d1]*x[2,d2]*A[3,d1,d2,j]);
s.t. I3 {i in Q, j in S[i]}: r[i,j] = t[i] - u[i,j];
s.t. I4 {i in Q, j in S[i]}: t[i] >= u[i,j];
s.t. I5 {i in Q, j in S[i]}: x[i,j] <= 1 - b[i,j];
s.t. I7 {i in Q, j in S[i]}: f[i,j] >= r[i,j];
s.t. I8 {i in Q, j in S[i]}: f[i,j] >= U[i]*b[i,j];
s.t. I10{i in Q, j in S[i]}: b[i,j]*b[i,j] = b[i,j];