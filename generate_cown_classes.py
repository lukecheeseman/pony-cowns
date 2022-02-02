def build_default_class(n):
  class_str = ""

  letters = [chr(ord("A") + i) for i in range(n)]
  generics = ", ".join(f"{letter}: Any #send" for letter in letters)
  class_str += f"class _When{n}[{generics}]\n"
  class_str += "  let _manager: Manager\n"
  for i in range(n):
    class_str += f"  let _c{i + 1}: Cown[{letters[i]}]\n"

  class_str += "\n"
  arguments = ", ".join(f"c{i + 1}: Cown[{letters[i]}]" for i in range(n))
  class_str += f"  new _create(manager: Manager tag, {arguments}) =>\n"
  class_str += f"    _manager = manager\n"
  assignments = "\n".join(f"    _c{i + 1} = c{i + 1}" for i in range(n))
  class_str += assignments

  class_str += "\n\n"
  lambda_args = ", ".join(letter for letter in letters)
  lambda_return = ", ".join(f"{letter}^" for letter in letters)
  class_str += f"  fun run(f: {{ref ({lambda_args}): ({lambda_return})}} iso) =>\n"
  class_str += f"    let body = Behaviour({n}, {{ref ()(cell = recover iso [ consume f ] end) =>\n"
  indent_str = "      "
  for i in range(n):
    popped_str = ", ".join(["let f"] + [f"let {letters[j].lower()}" for j in range(i - 1)])
    consume_str = ", ".join(["consume f"] + [f"consume {letters[j].lower()}" for j in range(i)])
    capture_cowns_str = ", ".join(f"_c{i + 1} = _c{i + 1}" for i in range(n))

    class_str += f"{indent_str}try\n"
    class_str += f"{indent_str}  ({popped_str}) = cell.pop()?\n"
    class_str += f"{indent_str}  _c{i+1}._empty({{ref ({letters[i].lower()}: {letters[i]})(cell = recover iso [ ({consume_str}) ] end, {capture_cowns_str}) =>\n"
    indent_str += "    "

  popped_str = ", ".join(["let f"] + [f"let {letters[i].lower()}" for i in range(n - 1)])
  result_tuple_str = ", ".join(f"let {letters[i].lower()}'" for i in range(n))
  consume_str = ", ".join(f"consume {letters[i].lower()}" for i in range(n))

  class_str += f"{indent_str}try\n"
  class_str += f"{indent_str}  ({popped_str}) = cell.pop()?\n"
  class_str += f"{indent_str}  ({result_tuple_str}) = f({consume_str})\n"
  for i in range(n):
    class_str += f"{indent_str}  _c{i + 1}._fill(consume {letters[i].lower()}')\n"

  for i in range(n):
    class_str += f"{indent_str}end\n"
    class_str += f"{indent_str[:-2]}}} iso)\n"
    indent_str = indent_str[:-4]

  class_str += f"{indent_str}end\n"
  class_str += f"{indent_str[:-2]}}} iso)\n"

  cowns = "; ".join(f"_c{i + 1}" for i in range(n))
  class_str += f"    _manager._send([{cowns}], body)"

  return class_str

def build_and_method(n):
  next_letter = chr(ord("A") + n)
  type_arguments = ", ".join(chr(ord("A") + i) for i in range(n + 1))
  arguments = ", ".join(f"_c{i + 1}" for i in range(n))
  method_str = f"  fun n[{next_letter}: Any #send](c{n + 1}: Cown[{next_letter}]): _When{n + 1}[{type_arguments}] => \n"
  return method_str + f"    _When{n + 1}[{type_arguments}]._create(_manager, {arguments}, c{n + 1})\n"

limit = 5
for i in range(limit):
  class_str = build_default_class(i + 1)

  if i != (limit - 1):
    class_str += "\n\n"
    class_str += build_and_method(i + 1)

  print(class_str)