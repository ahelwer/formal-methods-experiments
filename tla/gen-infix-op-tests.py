import json
import csv

f = open('src/node-types.json', 'r', encoding='utf-8')
node_types = json.load(f)
f.close()
f = open('../standard/unicode/tla-unicode.csv')
symbol_file = csv.DictReader(f)
symbols = {
    row['Name']: row['ASCII'].split(';')
    for row in symbol_file
}
f.close()
symbols['minusminus'] = ['--']
symbols['vert'] = ['|']
symbols['eq'] = ['=']
symbols['lt'] = ['<']
symbols['gt'] = ['>']
symbols['slash'] = ['/']
symbols['mod'] = ['%']
symbols['modmod'] = ['%%']
symbols['pow'] = ['^']
symbols['powpow'] = ['^^']
symbols['amp'] = ['&']
symbols['ampamp'] = ['&&']
symbols['minus'] = ['-']
symbols['slashslash'] = ['//']
symbols['mul'] = ['*']
symbols['mulmul'] = ['**']
symbols['plus'] = ['+']
symbols['hashhash'] = ['##']
symbols['map_to'] = [':>']
symbols['map_from'] = ['<:']
symbols['setminus'] = ['\\']
symbols['dol'] = ['$']
symbols['doldol'] = ['$$']
symbols['compose'] = ['@@']
symbols['plusplus'] = ['++']
names = [
    child['type']
    for child in next(
         item['children']['types']
         for item in node_types if item['type'] == 'infix_op_symbol'
    )
]
i = 0
for name in names:
    for symbol in symbols[name]:
        # Definition
        #print(f'x {symbol} y == {i}')
        #print(f'  (operator_definition parameter: (identifier) name: (infix_op_symbol ({name})) parameter: (identifier) (def_eq) definition: (nat_number))')
        # Declaration
        #print(f'  _ {symbol} _,')
        #print(f'    parameter: (operator_declaration (placeholder) name: (infix_op_symbol ({name})) (placeholder))')
        # Application
        #print(f'  x {symbol} y,')
        #print(f'    (bound_infix_op lhs: (identifier_ref) symbol: ({name}) rhs: (identifier_ref))')
        # Parameters
        #print(f'  {symbol},')
        #print(f'    parameter: (infix_op_symbol ({name}))')
        # Nonfix
        #print(f'  A!B!{symbol}(x, y),')
        #print(f'    (prefixed_op prefix: (subexpr_prefix (subexpr_component (identifier_ref)) (subexpr_component (identifier_ref))) op:\n      (bound_nonfix_op symbol: (infix_op_symbol ({name})) (identifier_ref) (identifier_ref)))')
        # SANY translator
        escaped_symbol = symbol.replace('\\', '\\\\')
        print(f'\t\t\tcase "{escaped_symbol}": return Kind.{name.upper()}.asNode();')
        i += 1

