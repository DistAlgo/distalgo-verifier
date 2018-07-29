# distalgo-action translator 
    TODO: Add desc

# Running the translator
  Script da2tla_action found in ./bin invokes the translation. To translate the da file, <SOURCE> to tla file <TARGET>, execute the following from ./bin directory:
    
    python da2tla_action <SOURCE> -o <TARGET>

  For example, to translate the fair_inc_action.da file in ./examples/lamutex, execute the following from ./bin directory:
    
    Windows: python da2tla_action ..\examples\lamutex\fair_inc_action.da -o ..\examples\lamutex\fair_inc_action.tla
    Unix: python da2tla_action ../examples/lamutex/fair_inc_action.da -o ../examples/lamutex/fair_inc_action.tla