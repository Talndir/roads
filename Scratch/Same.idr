module Scratch.Same

import Data.Vect

-- Prove that they have the same type
sameType : {x : a} -> {y : b} -> x = y -> (a = b)
sameType Refl = Refl

-- Take a heterogeneous equality and make a homogeneous one
forceSame : (eq : a = b)
         -> {x : a} -> {y : b}
         -> Equal {a = a} {b = b} x y
         -> Equal {a = a} {b = a} x (rewrite eq in y)
forceSame Refl Refl = Refl

rewriteEq : (eq : b = c)
         -> {x : a} -> {y : b}
         -> Equal {a = a} {b = b} x y
         -> Equal {a = a} {b = c} x (rewrite sym eq in y)
rewriteEq Refl Refl = Refl

-- For lists
sameLen : {xs : List a} -> {ys : List b} -> xs = ys -> length xs = length ys
sameLen pf = cong length (forceSame (sameType pf) pf)

-- For length-indexed vectors
sameLen' : {xs : Vect n a} -> {ys : Vect m b} -> xs = ys -> n = m
sameLen' pf = rewrite sym (lengthCorrect xs) in
              rewrite sym (lengthCorrect ys) in
              cong length (forceSame (sameType pf) pf)

top : {xs : List a} -> {ys : List b} -> xs = ys -> length xs = length ys
top Refl = Refl

top' : {xs : Vect n a} -> {ys : Vect m b} -> xs = ys -> n = m
top' Refl = Refl