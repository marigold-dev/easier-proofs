{
open Parser
exception SyntaxError of string
}

let whitechar = [' ' '\t' '\n']+
let digit = ['0'-'9']
let nat = digit+
let alpha = ['a'-'z' 'A'-'Z']
let id = alpha+digit*

rule read =
    parse
    | whitechar {read lexbuf}
    | "(" {LPAREN}
    | ")" {RPAREN}
    | "=" {EQUAL}
    | "<>" {DIFF}
    | "{" {LBRACKET}
    | "}" {RBRACKET}
    | "," {COMMA}
    | ":" {COLON}
    | ";" {SEMICOLON}
    | "-" {MINUS}
    | '"' {read_string (Buffer.create 17) lexbuf}
    | "straight" {STRAIGHT}
    | "case" {CASE}
    | "of" {OF}
    | "property" {PROP}
    | "properties" {PROPS}
    | id {ID (Lexing.lexeme lexbuf)}
    | nat {INT (int_of_string (Lexing.lexeme lexbuf))}
    | eof { EOF }

and read_string buf =
    parse
    | '"' {STRING (Buffer.contents buf)}
    | [^ '"']+ 
        {   Buffer.add_string buf (Lexing.lexeme lexbuf);
            read_string buf lexbuf
        }
    | _ {raise (SyntaxError ("Illegal character in string" ^ Lexing.lexeme lexbuf))}
    | eof {raise (SyntaxError ("string is not closed"))}