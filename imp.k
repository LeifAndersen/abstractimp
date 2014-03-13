module IMP-SYNTAX
  syntax AExp  ::= Int | Id
                 | AExp "/" AExp              [left, strict]
                 > AExp "+" AExp              [left, strict]
                 | "(" AExp ")"               [bracket]
  syntax BExp  ::= Bool
                 | AExp "<=" AExp             [seqstrict, latex({#1}\leq{#2})]
                 | "!" BExp                   [strict]
                 > BExp "&&" BExp             [left, strict(1)]
                 | "(" BExp ")"               [bracket]
  syntax Block ::= "{" "}"
                 | "{" Stmt "}"
  syntax Stmt  ::= Block
                 | Id "=" AExp ";"            [strict(2)]
                 | "if" "(" BExp ")"
                   Block "else" Block         [strict(1)]
                 | "while" "(" BExp ")" Block
                 > Stmt Stmt                  [left]
  syntax Pgm ::= "int" Ids ";" Stmt
  syntax Ids ::= List{Id,","}
endmodule


module IMP
  imports IMP-SYNTAX
  syntax KResult ::= Int | Bool | Aint | Abool

  syntax Aint  ::= "aint"
  syntax Abool ::= "abool"
  syntax AExp  ::= Aint
  syntax BExp  ::= Abool

  configuration <T color="yellow">
                  <k color="green"> $PGM:Pgm </k>
                  <state color="red">
                    <pair multiplicity="*" color="blue">
                      .Map
                    </pair>
                  </state>
                </T>

// AExp
  rule <k> X:Id => I ...</k> <state>... <pair> X |-> I </pair> ...</state> [lookup]
  rule I1:Int / I2:Int => I1 /Int I2  when I2 =/=Int 0
  arule aint / _ => aint
  arule _ / aint => aint
  rule I1:Int + I2:Int => I1 +Int I2
  arule aint + _ => aint
  arule _ + aint => aint
// BExp
  rule I1:Int <= I2:Int => I1 <=Int I2
  rule aint <= _ => abool
  rule _ <= aint => abool
  rule ! T:Bool => notBool T
  rule ! abool => abool
  rule true && B => B
  rule false && _ => false
  rule abool && false => false
  rule abool && true => abool
// Block
  rule {} => .   [structural]
  rule {S} => S  [structural]
// Stmt
  arule <k> X = I:Int; => . ...</k> <state>... <pair> X |-> (_ => aint) </pair> ...</state>
    when I >Int 100
  arule <k> X = I:Int; => . ...</k> <state>... <pair> X |-> (_ => I) </pair> ...</state>
    when I <=Int 100
  crule <k> X = I:Int; => . ...</k> <state>... <pair> X |-> (_ => I) </pair> ...</state>
  rule S1 S2 => S1 ~> S2  [structural]
  rule if (true)  S else _ => S
  rule if (false) _ else S => S
  rule if (abool) S1 else S2 => S1 [split]
  rule if (abool) S1 else S2 => S2 [split]
  rule while (B) S => if (B) {S while (B) S} else {}  [structural]
// Pgm
  rule <k> int (X:Id,Xs:Ids => Xs);_ </k> <state>... (. => <pair> X|->0 </pair>) ...</state>
  rule int .Ids; S => S  [structural]
endmodule
