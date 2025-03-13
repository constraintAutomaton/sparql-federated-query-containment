% knowledge
beta_b(x, a, undergradStudent) .
beta_b(x, takeCourse, y) .
beta_b(x, name, n) .
beta_b(x, phone, tel) .

beta_b(X, a, undergradStudent) :- X=x .
beta_b(X, takeCourse, Y) :- X=x, Y=y .
beta_b(_, name, _) :- beta_b(x, name, n) .
beta_b(_, phone, _) :- beta_b(x, phone, tel) .

% query 1

phi_1(Tel, X, Y, N):- 
    beta_b(X, a, undergradStudent),
    beta_b(X, takeCourse, Y),
    beta_b(X, name, N),
    beta_b(Y, name, N).


%theta_1(Tel, X, Y, N) :- \+ phi_1(Tel, X, Y, N) .

% query 2

phi_2(Tel, X, Y, N):- 
    beta_b(X, a, undergradStudent),
    beta_b(X, takeCourse, Y),
    beta_b(X, name, N),
    beta_b(X, phone, Tel), 
    Tel = "tim" .

%theta_2(Tel) :- \+ phi_2(Tel) .

forall(P, Q) :- \+ (P, \+ Q).
