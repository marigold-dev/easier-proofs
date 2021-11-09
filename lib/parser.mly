%{
open Ast
%}

%token <int> INT
%token <string> ID
%token <string> STRING
%token EQUAL
%token DIFF
%token PROP
%token PROPS
%token OF
%token LPAREN
%token RPAREN
%token LBRACKET // {
%token RBRACKET // }
%token COMMA // ,
%token SEMICOLON // ;
%token COLON // :
%token MINUS // -
%token STRAIGHT
%token CASE
%token EOF

%start <Ast.program> prog

%%

prog:
    | p = program; EOF { p }
    ;
program:
    | PROPS; OF; id = ID; LBRACKET; ps = properties_descr; RBRACKET { ASTProg (id, ps) }
    | PROP; OF; id = ID; LBRACKET; ass = assertion_descr; MINUS; ph = proof_helper; RBRACKET { ASTProg (id, [ASTProp (ass,ph)]) }
    ;

property_descr: assertion_descr; MINUS; proof_helper {ASTProp ($1,$3)};

properties_descr:
    | property_descr {[$1]}
    | property_descr; SEMICOLON; properties_descr {$1 :: $3}
    ;
assertion_descr:
    | id = ID; ag = option(args); COLON; ass = assertion { ASTAssertD (id,ag,ass) }
    ;
arg: LPAREN; name = ID; COLON; typ = ID; RPAREN {ASTArg (name,typ)};
args: arg {[$1]}
    | arg COMMA args {$1 :: $3}
    ;
assertion:
    | leftPartAssert = STRING; EQUAL; rightPartAssert = STRING { ASTAssert (leftPartAssert,Equal,rightPartAssert) }
    | leftPartAssert = STRING; DIFF; rightPartAssert = STRING { ASTAssert (leftPartAssert,Diff,rightPartAssert) }
    ;
proof_helper:
    | STRAIGHT { Straight }
    | CASE; i = INT { Case i }
    ;