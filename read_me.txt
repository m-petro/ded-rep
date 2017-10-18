1. generic_swap had been rewriten with help predicate, but it wasnt proved （｡･-･｡)
2. string_unescape:
    2.1 safety was proved in unescape_special and unescape_space, but safety doesnt want to be proved in unescape_octal and unescape_hex
                                                                                                                (because of << ??)
    2.2 specification of string_unescape in the process 
