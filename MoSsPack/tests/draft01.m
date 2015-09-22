

v01 = SAssemble[{Ax, Ay, Az}, {"x", "y", "z"}];
v02 = SAssemble[{Bx, By, Bw}, {"x", "y", "w"}];
Print[SDot[v01, v01]];
Print[SDot[v01, v02]];
Print[SDot[v02, v01]];

m01 = Association[
	"Matrix" -> {{Aax, Aay, Aau},{Abx, Aby, Abu},{Acx,Acy,Acu}},
	"Row Labels" -> {"a","b","c"},
	"Column Labels" -> {"x","y","u"}
	];

m02 = SAssemble[
	{{Bym,Byn,Byo},{Bxm,Bxn,Bxo},{Bsm,Bsn,Bso}},
	{"m","n","o"},
	{"y","x","s"}
	];

Print[m01 // SMatrixForm[#, Left]&];	
Print[v01 // STableForm[#,Center]&];
Print[SDot[m01,v01] // STableForm];
Print[m02 // SMatrixForm[#, Left]&];
Print[SDot[m01,m02] // SMatrixForm];

v0A = Association["Matrix" -> {Aa, Ab, Ac, Ad, Ax, Az}, 
  "Row Labels" -> {a, "b", c, "d", "X", z}]
v0B = Association["Matrix" -> {Bb, Bc, By, Bx, Bw}, 
  "Row Labels" -> {"b", c, y, "X", "w"}]
v0C = Association["Matrix" -> {Cb, Cs}, "Row Labels" -> {"b", "s"}, 
  "Column Labels" -> {"C"}]

Print[SAssemble[v0A,v0B,v0C] // STableForm]

m0A = <|"Matrix" -> Outer[Subscript[A, #1, #2] &, #1, #2], "Row Labels" -> #1, 
     "Column Labels" -> #2|> & @@ {{"a", "b", "c", "d"}, {"x", "y", "w"}};
Print[m0A // SMatrixForm];

m0B = <|"Matrix" -> 
      Outer[Subscript[B, #1, #2] &, #1, #2], "Row Labels" -> #1, 
     "Column Labels" -> #2|> & @@ {{"a", "c", "r", "s"}, {"z", "w", "y", "q"}};
Print[m0B // SMatrixForm];

m0C = SAssemble[m0A, m0B];
Print[m0C // SMatrixForm];

m0D = SDot[m0A, STranspose[m0B]];
Print[m0D // SMatrixForm];

m0E = SDot[m0B, STranspose[m0A]];
Print[m0E // SMatrixForm];

m0F = SDot[STranspose[m0A], m0B];
Print[m0F // SMatrixForm];

q01 = {x[t], y[t], z[t]};
qi01 = {x[t]^2+y[t]^2+z[t]^2};
qj01 = Jacobi[qi01, q01];
Print[qj01 // SMatrixForm];
Print[SDot[qj01, OrthogonalComplement[qj01, {x[t],z[t]}]] //SMatrixForm]
Print[STranspose @ qj01 // SMatrixForm]
Print[STranspose @ OrthogonalComplement[qj01, {x[t],z[t]}] // SMatrixForm]
Print[SDot[STranspose @ OrthogonalComplement[qj01, {x[t],z[t]}], STranspose @ qj01] //SMatrixForm]

Print[m0A ~SDot~ STranspose @ m0C //SMatrixForm]

Print[Homogeneous["Rx", "Tz"][x, s] // MatrixForm];
Print[Rotation["x", "y", "z"][x, y, z] /. {y -> 0, z -> 0} // MatrixForm];