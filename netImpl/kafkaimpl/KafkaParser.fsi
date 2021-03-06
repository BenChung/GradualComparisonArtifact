// Signature file for parser generated by fsyacc
type token = 
  | EOF
  | COLON
  | SEMICOLON
  | CLASS
  | OPAREN
  | CPAREN
  | OCURLY
  | CCURLY
  | ID of (string)
type tokenId = 
    | TOKEN_EOF
    | TOKEN_COLON
    | TOKEN_SEMICOLON
    | TOKEN_CLASS
    | TOKEN_OPAREN
    | TOKEN_CPAREN
    | TOKEN_OCURLY
    | TOKEN_CCURLY
    | TOKEN_ID
    | TOKEN_end_of_input
    | TOKEN_error
type nonTerminalId = 
    | NONTERM__startstart
    | NONTERM_start
    | NONTERM_program
    | NONTERM_clses
    | NONTERM_clss
    | NONTERM_expr
/// This function maps tokens to integer indexes
val tagOfToken: token -> int

/// This function maps integer indexes to symbolic token ids
val tokenTagToTokenId: int -> tokenId

/// This function maps production indexes returned in syntax errors to strings representing the non terminal that would be produced by that production
val prodIdxToNonTerminal: int -> nonTerminalId

/// This function gets the name of a token as a string
val token_to_string: token -> string
val start : (Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> token) -> Microsoft.FSharp.Text.Lexing.LexBuffer<'cty> -> (string) 
