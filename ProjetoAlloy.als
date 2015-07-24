module SistemaDePermissao

	sig Diretorio{
		diretoriopai: lone Diretorio
}
	fact {
		all d: Diretorio | d !in d.^diretoriopai
		all d: Diretorio | (d != Root) => (Root in d.^diretoriopai)
		no Root.diretoriopai
}

	sig Arquivo{
		diretorio: one Diretorio
}

	one sig Root extends Diretorio {}

	pred show[]{}
	run show for 3
