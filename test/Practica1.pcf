# Ejercicios apunte "El Lenguaje PCF".

# Ejercicio 1

# suma
let sum = fix (f:Nat->Nat->Nat) (m:Nat) -> fun(n:Nat) -> ifz n then m else succ (f m (pred n))
# resta
let res = fix (f:Nat->Nat->Nat) (m:Nat) -> fun(n:Nat) -> ifz n then m else pred (f m (pred n))
# multiplicación
let mul = fix (f:Nat->Nat->Nat) (m:Nat) -> fun(n:Nat) -> ifz n then 0 else (ifz m then 0 else (sum m (f m (pred n))))
# potencia
let pow = fix (f:Nat->Nat->Nat) (m:Nat) -> fun(n:Nat) -> ifz n then 1 else mul m (f m (pred n))
# factorial
let fact = fix (f:Nat->Nat) (m:Nat) -> ifz m then 1 else mul m (f (pred m))
# Fibonacci
let fib = fix (f: Nat->Nat) (m:Nat) -> ifz m then 0 else (ifz pred m then 1 else sum (f (pred m)) (f (pred (pred m))))

# Ejercicio 2

# Booleans:
let true  = 0
let false = 1
let ifthenelse = fun(c:Nat) -> fun(t1:Nat) -> fun(t2:Nat) -> ifz c then t1 else t2
let and = fun(a:Nat) -> fun(b:Nat) -> ifz a then (ifz b then 0 else 1) else 1
let or  = fun(a:Nat) -> fun(b:Nat) -> ifz a then 0 else (ifz b then 0 else 1)
let not = fun(a:Nat) -> ifz a then 1 else 0
let xor = fun(a:Nat) -> fun(b:Nat) -> or (and a b) (and (not a) (not b))

# Pairs:
let pair  = fun(a:Nat) -> fun(b:Nat) -> fun(f:Nat->Nat->Nat) -> f a b
let proj1 = fun(a:Nat) -> fun(b:Nat) -> a
let proj2 = fun(a:Nat) -> fun(b:Nat) -> b

# Ejercicio 3

# greater then or equal
let gte = fun(a:Nat) -> fun(b:Nat) -> ifz res b a then 0 else 1

# Algoritmo de Euclides
let gcd = fix (f:Nat->Nat->Nat) (m:Nat) -> fun(n:Nat) -> 
    ifz n 
    then m 
    else (ifz m 
          then n 
          else (ifz gte m n
                then f (res m n) n
                else f m (res n m)))

# Ejercicio 4

# R(Nat) :: Nat -> (Nat -> Nat -> Nat) -> (Nat -> Nat)
# R z s = 
#   | f 0        = z
#   | f (succ n) = s (f n) n

let R_nat = fun(z:Nat) -> fun(s:Nat->Nat->Nat) -> fix (f:Nat->Nat) (n:Nat) -> ifz n then z else s (f (pred n)) (pred n)