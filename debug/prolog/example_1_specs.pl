% knowledge
beta_b(_, a, undergradStudent) .
beta_b(_, takeCourse, _)  .
beta_b(_, name, _) .
beta_b(_, phone, _) .

% query 1

phi_1(Tel, X, Y, N):- 
    beta_b(X, a, undergradStudent),
    beta_b(X, takeCourse, Y),
    beta_b(Y, name, N),
    beta_b(X, name, N) .

theta_1(Tel, X, Y, N) :- \+ phi_1(Tel, X, Y, N) .

% query 2

phi_2(Tel, X, Y, N):- 
    beta_b(X, a, undergradStudent),
    beta_b(X, takeCourse, Y),
    beta_b(X, name, N),
    beta_b(X, phone, Tel), 
    Tel = "tim" .

%theta_2(Tel) :- \+ phi_2(Tel) .

forall(P, Q) :- \+ (P, \+ Q).
