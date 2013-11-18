-module(pegerl_parse).
-export([parse/1,file/1]).
-compile({nowarn_unused_function,[p/4, p/5, p_eof/0, p_optional/1, p_not/1, p_assert/1, p_seq/1, p_and/1, p_choose/1, p_zero_or_more/1, p_one_or_more/1, p_label/2, p_string/1, p_anything/0, p_charclass/1, p_regexp/1, p_attempt/4, line/1, column/1]}).



-spec file(file:name()) -> any().
file(Filename) -> case file:read_file(Filename) of {ok,Bin} -> parse(Bin); Err -> Err end.

-spec parse(binary() | list()) -> any().
parse(List) when is_list(List) -> parse(list_to_binary(List));
parse(Input) when is_binary(Input) ->
  setup_memo(),
  Result = case 'grammar'(Input,{{line,1},{column,1}}) of
             {AST, <<>>, _Index} -> AST;
             Any -> Any
           end,
  release_memo(), Result.

'grammar'(Input, Index) ->
  p(Input, Index, 'grammar', fun(I,D) -> (p_seq([fun '__'/2, p_label('initializer', p_optional(fun 'initializer'/2)), p_label('rules', p_one_or_more(fun 'rule'/2))]))(I,D) end, fun(Node, _Idx) ->Node end).

'initializer'(Input, Index) ->
  p(Input, Index, 'initializer', fun(I,D) -> (p_seq([p_label('code', fun 'action'/2), p_optional(fun 'semicolon'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

'rule'(Input, Index) ->
  p(Input, Index, 'rule', fun(I,D) -> (p_seq([p_label('name', fun 'identifier'/2), p_label('displayName', p_optional(fun 'string'/2)), fun 'equals'/2, p_label('expression', fun 'expression'/2), p_optional(fun 'semicolon'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

'expression'(Input, Index) ->
  p(Input, Index, 'expression', fun(I,D) -> (fun 'choice'/2)(I,D) end, fun(Node, _Idx) ->Node end).

'choice'(Input, Index) ->
  p(Input, Index, 'choice', fun(I,D) -> (p_seq([p_label('head', fun 'sequence'/2), p_label('tail', p_zero_or_more(p_seq([fun 'slash'/2, fun 'sequence'/2])))]))(I,D) end, fun(Node, _Idx) ->Node end).

'sequence'(Input, Index) ->
  p(Input, Index, 'sequence', fun(I,D) -> (p_choose([p_seq([p_label('elements', p_zero_or_more(fun 'labeled'/2)), p_label('code', fun 'action'/2)]), p_label('elements', p_zero_or_more(fun 'labeled'/2))]))(I,D) end, fun(Node, _Idx) ->Node end).

'labeled'(Input, Index) ->
  p(Input, Index, 'labeled', fun(I,D) -> (p_choose([p_seq([p_label('label', fun 'identifier'/2), fun 'colon'/2, p_label('expression', fun 'prefixed'/2)]), fun 'prefixed'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'prefixed'(Input, Index) ->
  p(Input, Index, 'prefixed', fun(I,D) -> (p_choose([p_seq([fun 'dollar'/2, p_label('expression', fun 'suffixed'/2)]), p_seq([fun 'and'/2, p_label('code', fun 'action'/2)]), p_seq([fun 'and'/2, p_label('expression', fun 'suffixed'/2)]), p_seq([fun 'not'/2, p_label('code', fun 'action'/2)]), p_seq([fun 'not'/2, p_label('expression', fun 'suffixed'/2)]), fun 'suffixed'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'suffixed'(Input, Index) ->
  p(Input, Index, 'suffixed', fun(I,D) -> (p_choose([p_seq([p_label('expression', fun 'primary'/2), fun 'question'/2]), p_seq([p_label('expression', fun 'primary'/2), fun 'star'/2]), p_seq([p_label('expression', fun 'primary'/2), fun 'plus'/2]), fun 'primary'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'primary'(Input, Index) ->
  p(Input, Index, 'primary', fun(I,D) -> (p_choose([p_seq([p_label('name', fun 'identifier'/2), p_not(p_seq([p_optional(fun 'string'/2), fun 'equals'/2]))]), fun 'literal'/2, fun 'class'/2, fun 'dot'/2, p_seq([fun 'lparen'/2, p_label('expression', fun 'expression'/2), fun 'rparen'/2])]))(I,D) end, fun(Node, _Idx) ->Node end).

'action'(Input, Index) ->
  p(Input, Index, 'action', fun(I,D) -> (p_seq([p_label('braced', fun 'braced'/2), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'braced'(Input, Index) ->
  p(Input, Index, 'braced', fun(I,D) -> (p_seq([p_string(<<"{">>), p_zero_or_more(p_choose([fun 'braced'/2, fun 'nonBraceCharacters'/2])), p_string(<<"}">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

'nonBraceCharacters'(Input, Index) ->
  p(Input, Index, 'nonBraceCharacters', fun(I,D) -> (p_one_or_more(fun 'nonBraceCharacter'/2))(I,D) end, fun(Node, _Idx) ->Node end).

'nonBraceCharacter'(Input, Index) ->
  p(Input, Index, 'nonBraceCharacter', fun(I,D) -> (p_charclass(<<"[^{}]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'equals'(Input, Index) ->
  p(Input, Index, 'equals', fun(I,D) -> (p_seq([p_string(<<"=">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'colon'(Input, Index) ->
  p(Input, Index, 'colon', fun(I,D) -> (p_seq([p_string(<<":">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'semicolon'(Input, Index) ->
  p(Input, Index, 'semicolon', fun(I,D) -> (p_seq([p_string(<<";">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'slash'(Input, Index) ->
  p(Input, Index, 'slash', fun(I,D) -> (p_seq([p_string(<<"\/">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'and'(Input, Index) ->
  p(Input, Index, 'and', fun(I,D) -> (p_seq([p_string(<<"&">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'not'(Input, Index) ->
  p(Input, Index, 'not', fun(I,D) -> (p_seq([p_string(<<"!">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'dollar'(Input, Index) ->
  p(Input, Index, 'dollar', fun(I,D) -> (p_seq([p_string(<<"$">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'question'(Input, Index) ->
  p(Input, Index, 'question', fun(I,D) -> (p_seq([p_string(<<"?">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'star'(Input, Index) ->
  p(Input, Index, 'star', fun(I,D) -> (p_seq([p_string(<<"*">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'plus'(Input, Index) ->
  p(Input, Index, 'plus', fun(I,D) -> (p_seq([p_string(<<"+">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'lparen'(Input, Index) ->
  p(Input, Index, 'lparen', fun(I,D) -> (p_seq([p_string(<<"(">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'rparen'(Input, Index) ->
  p(Input, Index, 'rparen', fun(I,D) -> (p_seq([p_string(<<")">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'dot'(Input, Index) ->
  p(Input, Index, 'dot', fun(I,D) -> (p_seq([p_string(<<".">>), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'identifier'(Input, Index) ->
  p(Input, Index, 'identifier', fun(I,D) -> (p_seq([p_label('chars', p_seq([p_choose([fun 'letter'/2, p_string(<<"_">>)]), p_zero_or_more(p_choose([fun 'letter'/2, fun 'digit'/2, p_string(<<"_">>)]))])), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'literal'(Input, Index) ->
  p(Input, Index, 'literal', fun(I,D) -> (p_seq([p_label('value', p_choose([fun 'doubleQuotedString'/2, fun 'singleQuotedString'/2])), p_label('flags', p_optional(p_string(<<"i">>))), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'string'(Input, Index) ->
  p(Input, Index, 'string', fun(I,D) -> (p_seq([p_label('string', p_choose([fun 'doubleQuotedString'/2, fun 'singleQuotedString'/2])), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'doubleQuotedString'(Input, Index) ->
  p(Input, Index, 'doubleQuotedString', fun(I,D) -> (p_seq([p_string(<<"\"">>), p_label('chars', p_zero_or_more(fun 'doubleQuotedCharacter'/2)), p_string(<<"\"">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

'doubleQuotedCharacter'(Input, Index) ->
  p(Input, Index, 'doubleQuotedCharacter', fun(I,D) -> (p_choose([fun 'simpleDoubleQuotedCharacter'/2, fun 'simpleEscapeSequence'/2, fun 'zeroEscapeSequence'/2, fun 'hexEscapeSequence'/2, fun 'unicodeEscapeSequence'/2, fun 'eolEscapeSequence'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'simpleDoubleQuotedCharacter'(Input, Index) ->
  p(Input, Index, 'simpleDoubleQuotedCharacter', fun(I,D) -> (p_seq([p_not(p_choose([p_string(<<"\"">>), p_string(<<"\\">>), fun 'eolChar'/2])), p_label('char_', p_anything())]))(I,D) end, fun(Node, _Idx) ->Node end).

'singleQuotedString'(Input, Index) ->
  p(Input, Index, 'singleQuotedString', fun(I,D) -> (p_seq([p_string(<<"\'">>), p_label('chars', p_zero_or_more(fun 'singleQuotedCharacter'/2)), p_string(<<"\'">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

'singleQuotedCharacter'(Input, Index) ->
  p(Input, Index, 'singleQuotedCharacter', fun(I,D) -> (p_choose([fun 'simpleSingleQuotedCharacter'/2, fun 'simpleEscapeSequence'/2, fun 'zeroEscapeSequence'/2, fun 'hexEscapeSequence'/2, fun 'unicodeEscapeSequence'/2, fun 'eolEscapeSequence'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'simpleSingleQuotedCharacter'(Input, Index) ->
  p(Input, Index, 'simpleSingleQuotedCharacter', fun(I,D) -> (p_seq([p_not(p_choose([p_string(<<"\'">>), p_string(<<"\\">>), fun 'eolChar'/2])), p_label('char_', p_anything())]))(I,D) end, fun(Node, _Idx) ->Node end).

'class'(Input, Index) ->
  p(Input, Index, 'class', fun(I,D) -> (p_seq([p_string(<<"[">>), p_optional(p_string(<<"^">>)), p_label('parts', p_zero_or_more(p_choose([fun 'classCharacterRange'/2, fun 'classCharacter'/2]))), p_string(<<"]">>), p_label('flags', p_optional(p_string(<<"i">>))), fun '__'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'classCharacterRange'(Input, Index) ->
  p(Input, Index, 'classCharacterRange', fun(I,D) -> (p_seq([p_label('begin', fun 'classCharacter'/2), p_string(<<"-">>), p_label('end', fun 'classCharacter'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

'classCharacter'(Input, Index) ->
  p(Input, Index, 'classCharacter', fun(I,D) -> (fun 'bracketDelimitedCharacter'/2)(I,D) end, fun(Node, _Idx) ->Node end).

'bracketDelimitedCharacter'(Input, Index) ->
  p(Input, Index, 'bracketDelimitedCharacter', fun(I,D) -> (p_choose([fun 'simpleBracketDelimitedCharacter'/2, fun 'simpleEscapeSequence'/2, fun 'zeroEscapeSequence'/2, fun 'hexEscapeSequence'/2, fun 'unicodeEscapeSequence'/2, fun 'eolEscapeSequence'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'simpleBracketDelimitedCharacter'(Input, Index) ->
  p(Input, Index, 'simpleBracketDelimitedCharacter', fun(I,D) -> (p_seq([p_not(p_choose([p_string(<<"]">>), p_string(<<"\\">>), fun 'eolChar'/2])), p_label('char_', p_anything())]))(I,D) end, fun(Node, _Idx) ->Node end).

'simpleEscapeSequence'(Input, Index) ->
  p(Input, Index, 'simpleEscapeSequence', fun(I,D) -> (p_seq([p_string(<<"\\">>), p_not(p_choose([fun 'digit'/2, p_string(<<"x">>), p_string(<<"u">>), fun 'eolChar'/2])), p_label('char_', p_anything())]))(I,D) end, fun(Node, _Idx) ->Node end).

'zeroEscapeSequence'(Input, Index) ->
  p(Input, Index, 'zeroEscapeSequence', fun(I,D) -> (p_seq([p_string(<<"\\0">>), p_not(fun 'digit'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

'hexEscapeSequence'(Input, Index) ->
  p(Input, Index, 'hexEscapeSequence', fun(I,D) -> (p_seq([p_string(<<"\\x">>), p_label('digits', p_seq([fun 'hexDigit'/2, fun 'hexDigit'/2]))]))(I,D) end, fun(Node, _Idx) ->Node end).

'unicodeEscapeSequence'(Input, Index) ->
  p(Input, Index, 'unicodeEscapeSequence', fun(I,D) -> (p_seq([p_string(<<"\\u">>), p_label('digits', p_seq([fun 'hexDigit'/2, fun 'hexDigit'/2, fun 'hexDigit'/2, fun 'hexDigit'/2]))]))(I,D) end, fun(Node, _Idx) ->Node end).

'eolEscapeSequence'(Input, Index) ->
  p(Input, Index, 'eolEscapeSequence', fun(I,D) -> (p_seq([p_string(<<"\\">>), p_label('eol', fun 'eol'/2)]))(I,D) end, fun(Node, _Idx) ->Node end).

'digit'(Input, Index) ->
  p(Input, Index, 'digit', fun(I,D) -> (p_charclass(<<"[0-9]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'hexDigit'(Input, Index) ->
  p(Input, Index, 'hexDigit', fun(I,D) -> (p_charclass(<<"[0-9a-fA-F]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'letter'(Input, Index) ->
  p(Input, Index, 'letter', fun(I,D) -> (p_choose([fun 'lowerCaseLetter'/2, fun 'upperCaseLetter'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'lowerCaseLetter'(Input, Index) ->
  p(Input, Index, 'lowerCaseLetter', fun(I,D) -> (p_charclass(<<"[a-z]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'upperCaseLetter'(Input, Index) ->
  p(Input, Index, 'upperCaseLetter', fun(I,D) -> (p_charclass(<<"[A-Z]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'__'(Input, Index) ->
  p(Input, Index, '__', fun(I,D) -> (p_zero_or_more(p_choose([fun 'whitespace'/2, fun 'eol'/2, fun 'comment'/2])))(I,D) end, fun(Node, _Idx) ->Node end).

'comment'(Input, Index) ->
  p(Input, Index, 'comment', fun(I,D) -> (p_choose([fun 'singleLineComment'/2, fun 'multiLineComment'/2]))(I,D) end, fun(Node, _Idx) ->Node end).

'singleLineComment'(Input, Index) ->
  p(Input, Index, 'singleLineComment', fun(I,D) -> (p_seq([p_string(<<"\/\/">>), p_zero_or_more(p_seq([p_not(fun 'eolChar'/2), p_anything()]))]))(I,D) end, fun(Node, _Idx) ->Node end).

'multiLineComment'(Input, Index) ->
  p(Input, Index, 'multiLineComment', fun(I,D) -> (p_seq([p_string(<<"\/*">>), p_zero_or_more(p_seq([p_not(p_string(<<"*\/">>)), p_anything()])), p_string(<<"*\/">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

'eol'(Input, Index) ->
  p(Input, Index, 'eol', fun(I,D) -> (p_choose([p_string(<<"\n">>), p_string(<<"\r\n">>), p_string(<<"\r">>), p_string(<<"\u2028">>), p_string(<<"\u2029">>)]))(I,D) end, fun(Node, _Idx) ->Node end).

'eolChar'(Input, Index) ->
  p(Input, Index, 'eolChar', fun(I,D) -> (p_charclass(<<"[\n\r\u2028\u2029]">>))(I,D) end, fun(Node, _Idx) ->Node end).

'whitespace'(Input, Index) ->
  p(Input, Index, 'whitespace', fun(I,D) -> (p_charclass(<<"[\s\t\v\f\u00A0\uFEFF\u1680\u180E\u2000-\u200A\u202F\u205F\u3000]">>))(I,D) end, fun(Node, _Idx) ->Node end).




p(Inp, Index, Name, ParseFun) ->
  p(Inp, Index, Name, ParseFun, fun(N, _Idx) -> N end).

p(Inp, StartIndex, Name, ParseFun, TransformFun) ->
  case get_memo(StartIndex, Name) of      % See if the current reduction is memoized
    {ok, Memo} -> %Memo;                     % If it is, return the stored result
      Memo;
    _ ->                                        % If not, attempt to parse
      Result = case ParseFun(Inp, StartIndex) of
        {fail,_} = Failure ->                       % If it fails, memoize the failure
          Failure;
        {Match, InpRem, NewIndex} ->               % If it passes, transform and memoize the result.
          Transformed = TransformFun(Match, StartIndex),
          {Transformed, InpRem, NewIndex}
      end,
      memoize(StartIndex, Name, Result),
      Result
  end.

setup_memo() ->
  put({parse_memo_table, ?MODULE}, ets:new(?MODULE, [set])).

release_memo() ->
  ets:delete(memo_table_name()).

memoize(Index, Name, Result) ->
  Memo = case ets:lookup(memo_table_name(), Index) of
              [] -> [];
              [{Index, Plist}] -> Plist
         end,
  ets:insert(memo_table_name(), {Index, [{Name, Result}|Memo]}).

get_memo(Index, Name) ->
  case ets:lookup(memo_table_name(), Index) of
    [] -> {error, not_found};
    [{Index, Plist}] ->
      case proplists:lookup(Name, Plist) of
        {Name, Result}  -> {ok, Result};
        _  -> {error, not_found}
      end
    end.

memo_table_name() ->
    get({parse_memo_table, ?MODULE}).

p_eof() ->
  fun(<<>>, Index) -> {eof, [], Index};
     (_, Index) -> {fail, {expected, eof, Index}} end.

p_optional(P) ->
  fun(Input, Index) ->
      case P(Input, Index) of
        {fail,_} -> {[], Input, Index};
        {_, _, _} = Success -> Success
      end
  end.

p_not(P) ->
  fun(Input, Index)->
      case P(Input,Index) of
        {fail,_} ->
          {[], Input, Index};
        {Result, _, _} -> {fail, {expected, {no_match, Result},Index}}
      end
  end.

p_assert(P) ->
  fun(Input,Index) ->
      case P(Input,Index) of
        {fail,_} = Failure-> Failure;
        _ -> {[], Input, Index}
      end
  end.

p_and(P) ->
  p_seq(P).

p_seq(P) ->
  fun(Input, Index) ->
      p_all(P, Input, Index, [])
  end.

p_all([], Inp, Index, Accum ) -> {lists:reverse( Accum ), Inp, Index};
p_all([P|Parsers], Inp, Index, Accum) ->
  case P(Inp, Index) of
    {fail, _} = Failure -> Failure;
    {Result, InpRem, NewIndex} -> p_all(Parsers, InpRem, NewIndex, [Result|Accum])
  end.

p_choose(Parsers) ->
  fun(Input, Index) ->
      p_attempt(Parsers, Input, Index, none)
  end.

p_attempt([], _Input, _Index, Failure) -> Failure;
p_attempt([P|Parsers], Input, Index, FirstFailure)->
  case P(Input, Index) of
    {fail, _} = Failure ->
      case FirstFailure of
        none -> p_attempt(Parsers, Input, Index, Failure);
        _ -> p_attempt(Parsers, Input, Index, FirstFailure)
      end;
    Result -> Result
  end.

p_zero_or_more(P) ->
  fun(Input, Index) ->
      p_scan(P, Input, Index, [])
  end.

p_one_or_more(P) ->
  fun(Input, Index)->
      Result = p_scan(P, Input, Index, []),
      case Result of
        {[_|_], _, _} ->
          Result;
        _ ->
          {fail, {expected, Failure, _}} = P(Input,Index),
          {fail, {expected, {at_least_one, Failure}, Index}}
      end
  end.

p_label(Tag, P) ->
  fun(Input, Index) ->
      case P(Input, Index) of
        {fail,_} = Failure ->
           Failure;
        {Result, InpRem, NewIndex} ->
          {{Tag, Result}, InpRem, NewIndex}
      end
  end.

p_scan(_, [], Index, Accum) -> {lists:reverse( Accum ), [], Index};
p_scan(P, Inp, Index, Accum) ->
  case P(Inp, Index) of
    {fail,_} -> {lists:reverse(Accum), Inp, Index};
    {Result, InpRem, NewIndex} -> p_scan(P, InpRem, NewIndex, [Result | Accum])
  end.

p_string(S) when is_list(S) -> p_string(list_to_binary(S));
p_string(S) ->
    Length = erlang:byte_size(S),
    fun(Input, Index) ->
      try
          <<S:Length/binary, Rest/binary>> = Input,
          {S, Rest, p_advance_index(S, Index)}
      catch
          error:{badmatch,_} -> {fail, {expected, {string, S}, Index}}
      end
    end.

p_anything() ->
  fun(<<>>, Index) -> {fail, {expected, any_character, Index}};
     (Input, Index) when is_binary(Input) ->
          <<C/utf8, Rest/binary>> = Input,
          {<<C/utf8>>, Rest, p_advance_index(<<C/utf8>>, Index)}
  end.

p_charclass(Class) ->
    {ok, RE} = re:compile(Class, [unicode, dotall]),
    fun(Inp, Index) ->
            case re:run(Inp, RE, [anchored]) of
                {match, [{0, Length}|_]} ->
                    {Head, Tail} = erlang:split_binary(Inp, Length),
                    {Head, Tail, p_advance_index(Head, Index)};
                _ -> {fail, {expected, {character_class, binary_to_list(Class)}, Index}}
            end
    end.

p_regexp(Regexp) ->
    {ok, RE} = re:compile(Regexp, [unicode, dotall, anchored]),
    fun(Inp, Index) ->
        case re:run(Inp, RE) of
            {match, [{0, Length}|_]} ->
                {Head, Tail} = erlang:split_binary(Inp, Length),
                {Head, Tail, p_advance_index(Head, Index)};
            _ -> {fail, {expected, {regexp, binary_to_list(Regexp)}, Index}}
        end
    end.

line({{line,L},_}) -> L;
line(_) -> undefined.

column({_,{column,C}}) -> C;
column(_) -> undefined.

p_advance_index(MatchedInput, Index) when is_list(MatchedInput) orelse is_binary(MatchedInput)-> % strings
  lists:foldl(fun p_advance_index/2, Index, unicode:characters_to_list(MatchedInput));
p_advance_index(MatchedInput, Index) when is_integer(MatchedInput) -> % single characters
  {{line, Line}, {column, Col}} = Index,
  case MatchedInput of
    $\n -> {{line, Line+1}, {column, 1}};
    _ -> {{line, Line}, {column, Col+1}}
  end.
