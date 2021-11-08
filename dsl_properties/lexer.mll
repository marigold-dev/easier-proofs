{
open Parser
exception SyntaxError of string
}

let whitechar = [' ' '\t' '\n']+
let digit = ['0'-'9']
let nat = digit+
let alphanum = ['a'-'z' 'A'-'Z' '0'-'9']
let id = alphanum+

rule read =
    parse
    | whitechar {read lexbuf}
    | "(" {Format.eprintf "LPAREN\n"; LPAREN}
    | ")" {Format.eprintf "RPAREN\n";RPAREN}
    | "=" {Format.eprintf "EQUAL\n";EQUAL}
    | "<>" {Format.eprintf "DIFF\n";DIFF}
    | "{" {Format.eprintf "LBRACKET\n";LBRACKET}
    | "}" {Format.eprintf "RBRACKET\n";RBRACKET}
    | "," {Format.eprintf "COMMA\n";COMMA}
    | ":" {Format.eprintf "COLON\n";COLON}
    | ";" {Format.eprintf "SEMICOLON\n";SEMICOLON}
    | "-" {Format.eprintf "MINUS\n";MINUS}
    | '"' { read_string (Buffer.create 17) lexbuf}
    | "straight" {Format.eprintf "STRAIGHT\n";STRAIGHT}
    | "case" {Format.eprintf "CASE\n";CASE}
    | "of" {Format.eprintf "OF\n";OF}
    | "property" {Format.eprintf "PROP\n";PROP}
    | "properties" {Format.eprintf "PROPS\n";PROPS}
    | id {Format.eprintf "ID\n";ID (Lexing.lexeme lexbuf)}
    | nat {Format.eprintf "INT\n";INT (int_of_string (Lexing.lexeme lexbuf))}
    | eof {Format.eprintf "EOF\n"; EOF }

and read_string buf =
    parse
    | '"' {STRING (Buffer.contents buf)}
    | [^ '"']+ 
        {   Buffer.add_string buf (Lexing.lexeme lexbuf);
            read_string buf lexbuf
        }
    | _ {raise (SyntaxError ("Illegal character in string" ^ Lexing.lexeme lexbuf))}
    | eof {raise (SyntaxError ("string is not closed"))}