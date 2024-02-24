module Eval

type ENV = Map<string, Background.VALUE>

val eval_name    : (Signature.NAME -> State.STATE -> Background.VALUE list -> Background.VALUE)

val eval_term    : (AST.TERM -> State.STATE * ENV -> Background.VALUE)

val eval_rule    : (AST.RULE -> State.STATE * ENV -> Updates.UPDATE_SET)


