using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class CubeSimplexDeterminantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The absolute augmented determinant on a cube is bounded by its largest value on sign matrices.",
        H("CubeSimplexDeterminant"),
        Blocks(
            Describe.Lean(DescribeId.Create("signmatrix"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.signMatrix"),
                H("signMatrix"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("V"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Call("Bool"))), Comma, Sp, Seq(Seq(Call("signMatrix"), Sp, F.Id("d"), Sp, F.Id("V")), Sp, Eq, Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Mapsto, Sp, Call("if"), Sp, F.Id("V"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Call("then"), Sp, D(1), Sp, Call("else"), Sp, Minus, Sp, D(1)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("delta"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.delta"),
                H("delta"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Seq(Call("delta"), Sp, F.Id("d")), Sp, Eq, Sp, Parenthesized(Seq(Call("Finset"), Sp, Dot, Sp, Call("univ"), Sp, Dot, Sp, Call("sup"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("V"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Call("Bool"), Sp, Mapsto, Sp, Parenthesized(Seq(Call("augment"), Sp, Parenthesized(Seq(Call("signMatrix"), Sp, F.Id("d"), Sp, F.Id("V"))))), Sp, Dot, Sp, Call("det"), Sp, Dot, Sp, Call("natAbs"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("augment-map"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.augment_map"),
                H("augment map"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("R"), Sp, F.Id("S"), Sp, Colon, Sp, Call("Type")), CloseBrace), Comma, Sp, Seq(Seq(OpenBracket, Seq(Call("CommRing"), Sp, F.Id("R")), CloseBracket), Sp, Seq(Seq(OpenBracket, Seq(Call("CommRing"), Sp, F.Id("S")), CloseBracket), Sp, Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("f"), Sp, Colon, Sp, Call("RingHom"), Sp, F.Id("R"), Sp, F.Id("S"))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, F.Id("R"))), Comma, Sp, Seq(Call("augment"), Sp, Parenthesized(Seq(F.Id("M"), Sp, Dot, Sp, Call("map"), Sp, F.Id("f"))), Sp, Eq, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("map"), Sp, F.Id("f")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmented-det-smul"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_smul"),
                H("augmented det smul"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("R"), Sp, Colon, Sp, Call("Type")), CloseBrace), Comma, Sp, Seq(Seq(OpenBracket, Seq(Call("CommRing"), Sp, F.Id("R")), CloseBracket), Sp, Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, F.Id("R"))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, F.Id("R"))), Comma, Sp, Seq(Parenthesized(Seq(Call("augment"), Sp, Parenthesized(Seq(F.Id("c"), Sp, Cdot, Sp, F.Id("M"))))), Sp, Dot, Sp, Call("det"), Sp, Eq, Sp, Sp, new Formula.Power(F.Id("c"), F.Id("d")), Sp, Star, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmented-det-integer-box-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_integer_box_bound"),
                H("augmented det integer box bound"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Parenthesized(Seq(D(1), Sp, Le, Sp, F.Id("m"))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("i"), Sp, F.Id("j"), Sp, Comma, Sp, Bar, Sp, F.Id("M"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Bar, Sp, Le, Sp, F.Id("m"))), Sp, To, Sp, Seq(Bar, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"), Sp, Bar, Sp, Le, Sp, Parenthesized(Seq(Call("delta"), Sp, F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Sp, Star, Sp, Sp, new Formula.Power(Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), F.Id("d"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmented-det-affine"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.augmented_det_affine"),
                H("augmented det affine"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("R"), Sp, Colon, Sp, Call("Type")), CloseBrace), Comma, Sp, Seq(Seq(OpenBracket, Seq(Call("CommRing"), Sp, F.Id("R")), CloseBracket), Sp, Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("c"), Sp, Colon, Sp, F.Id("R"))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("a"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("d"), Sp, To, Sp, F.Id("R"))), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, F.Id("R"))), Comma, Sp, Seq(Parenthesized(Seq(Call("augment"), Sp, Parenthesized(Seq(Call("Matrix"), Sp, Dot, Sp, Call("of"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Mapsto, Sp, F.Id("c"), Sp, Star, Sp, F.Id("M"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Plus, Sp, F.Id("a"), Sp, F.Id("i"))))))), Sp, Dot, Sp, Call("det"), Sp, Eq, Sp, Sp, new Formula.Power(F.Id("c"), F.Id("d")), Sp, Star, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det")))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("exists-maximizing-sign-simplex"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.exists_maximizing_sign_simplex"),
                H("exists maximizing sign simplex"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Parenthesized(Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Exists, Sp, F.Id("V"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Comma, Sp, Parenthesized(Seq(Forall, Sp, F.Id("i"), Sp, F.Id("j"), Sp, Comma, Sp, Bar, Sp, F.Id("V"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Bar, Sp, Le, Sp, D(1))), Sp, Land, Sp, Bar, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("V"))), Sp, Dot, Sp, Call("det"), Sp, Bar, Sp, Eq, Sp, Call("delta"), Sp, F.Id("d"), Sp, Land, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("V"))), Sp, Dot, Sp, Call("det"), Sp, Neq, Sp, D(0), Sp, Land, Sp, Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, D(0), Sp, Le, Sp, Parenthesized(Seq(Call("augment"), Sp, F.Id("V"))), Sp, Dot, Sp, Call("det"), Sp, Star, Sp, Call("cofactor"), Sp, F.Id("V"), Sp, F.Id("j"))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("primitive-cofactor-admissible"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/CubeSimplexDeterminant.primitive_cofactor_admissible"),
                H("primitive cofactor admissible"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("i"), Sp, F.Id("j"), Sp, Comma, Sp, Bar, Sp, F.Id("M"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Bar, Sp, Le, Sp, F.Id("m"))), Sp, To, Sp, Seq(Parenthesized(Seq(Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("s"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("s"), Sp, Eq, Sp, D(1), Sp, Lor, Sp, F.Id("s"), Sp, Eq, Sp, Minus, Sp, D(1))), Sp, To, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("j"), Sp, Comma, Sp, D(0), Sp, Lt, Sp, F.Id("s"), Sp, Star, Sp, Call("cofactor"), Sp, F.Id("M"), Sp, F.Id("j"))), Sp, To, Sp, Seq(Parenthesized(Seq(Call("Finset"), Sp, Dot, Sp, Call("univ"), Sp, Dot, Sp, Call("gcd"), Sp, Parenthesized(Seq(Call("cofactor"), Sp, F.Id("M"))), Sp, Eq, Sp, D(1))), Sp, To, Sp, Seq(Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"), Sp, Dot, Sp, Call("natAbs"), Sp, InMacro, Sp, Call("lengths"), Sp, F.Id("d"), Sp, F.Id("m"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1)))))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The absolute augmented determinant on a cube is bounded by its largest value on sign matrices."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
