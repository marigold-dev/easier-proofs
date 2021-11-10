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
    | properties_blocks {ASTProg ($1)}
    ;
properties_blocks:
    | propertie_block {[$1]}
    | propertie_block properties_blocks {$1 :: $2}
    ;
propertie_block:
    | PROPS; OF; id = ID; LBRACKET; assertions; RBRACKET { ASTPropsBlock (id, $5) }
    | PROP; OF; id = ID; LBRACKET; assertion_annoted RBRACKET { ASTPropsBlock (id, [$5]) }
    ;
assertions:
    | assertion_annoted {[$1]}
    | assertion_annoted; SEMICOLON; assertions {$1 :: $3}
    ;
assertion_annoted: id = ID; ag = option(args); COLON; ass = assertion; MINUS; ph = proof_helper { ASTAssertAn (id,ag,ass,ph) };
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