start : transform start | EOF;

transform : ID '=' expr

expr
    : num_expr                                                  # num_expr
    | bin_expr                                                  # bin_expr
    | '(' expr ')'                                              # enclose_expr
    ;

num_expr
    : num                                                       # number
    | num_expr '*' num_expr                                     # multi_expr
    | num_expr '+' num_expr                                     # add_expr
    | num_expr '-' num_expr                                     # sub_expr
    ;

bin_expr
    : bool_literal
    | unary_op bin_expr
    | num_expr '<' num_expr
    | num_expr '==' num_expr
    | num_expr '!=' num_expr
    | bin_expr LogicalAnd bin_expr
    | bin_expr LogicalOr bin_expr
    ;

unary_op : 'not' | '!' | '~' ;

num :
    literal
    | ID
    | ID '[' num ']'
    | ID '.' ID;

literal
    : StringLiteral
    | Digits
    ;

StringLiteral
    : \" NONDIGIT+ \"
    | \' NONDIGIT+ \'
    ;
Digits : DIGIT+;
bool_literal : 'True' | 'False' ;


LogicalAnd : ('and'    | '&&' );
LogicalOr  : ('or' | '||');

fragment NONDIGIT   : [a-zA-Z_\-];
fragment START_CHAR : [a-zA-Z_];
fragment DIGIT : [0-9];
ID : START_CHAR (NONDIGIT | DIGIT)* ;
