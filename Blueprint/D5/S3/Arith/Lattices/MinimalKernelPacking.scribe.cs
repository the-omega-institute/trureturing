using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Lattices;

internal sealed class MinimalKernelPackingDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube.",
        H("MinimalKernelPacking"),
        Blocks(
            Describe.Lean(DescribeId.Create("minimal-kernel-rank-deficient-bound"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/MinimalKernelPacking.minimal_kernel_rank_deficient_bound"),
                H("minimal kernel rank deficient bound"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("r"), Sp, F.Id("k"), Sp, F.Id("m"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1))))), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("k"))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("i"), Sp, F.Id("j"), Sp, Comma, Sp, Bar, Sp, F.Id("M"), Sp, F.Id("i"), Sp, F.Id("j"), Sp, Bar, Sp, Le, Sp, F.Id("m"))), Sp, To, Sp, Seq(Parenthesized(Seq(Neg, Sp, Call("Function"), Sp, Dot, Sp, Call("Injective"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("z"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(F.Id("r"), Sp, Plus, Sp, D(1))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Mapsto, Sp, F.Id("M"), Sp, Dot, Sp, Call("transpose"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, F.Id("z"))))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("k"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))))), Comma, Sp, Seq(Parenthesized(Seq(D(0), Sp, Lt, Sp, Sum, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("x"), Sp, F.Id("j"))), Sp, To, Sp, Seq(Parenthesized(Seq(F.Id("M"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("j"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("x"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Eq, Sp, D(0))), Sp, To, Sp, Seq(Parenthesized(Seq(Forall, Sp, F.Id("y"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("k"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("N"))), Sp, Comma, Sp, F.Id("y"), Sp, Le, Sp, F.Id("x"), Sp, To, Sp, F.Id("M"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("j"), Sp, Mapsto, Sp, Parenthesized(Seq(F.Id("y"), Sp, F.Id("j"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Z"))))))), Sp, Eq, Sp, D(0), Sp, To, Sp, F.Id("y"), Sp, Eq, Sp, D(0), Sp, Lor, Sp, F.Id("y"), Sp, Eq, Sp, F.Id("x"))), Sp, To, Sp, Seq(Sum, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("x"), Sp, F.Id("j"), Sp, Le, Sp, Sp, new Formula.Power(Parenthesized(Seq(D(2), Sp, Star, Sp, F.Id("k"), Sp, Star, Sp, F.Id("m"), Sp, Plus, Sp, D(1))), F.Id("r")), Sp, Star, Sp, F.Id("k")))))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("transpose-injective-of-augmented-det"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/MinimalKernelPacking.transpose_injective_of_augmented_det"),
                H("transpose injective of augmented det"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Seq(Call("Function"), Sp, Dot, Sp, Call("Injective"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("z"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Mapsto, Sp, F.Id("M"), Sp, Dot, Sp, Call("transpose"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, F.Id("z"))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("augmented-det-ne-zero-of-full-rank-positive"),
                DeclarationHandle.Create("D5/S3/Arith/Lattices/MinimalKernelPacking.augmented_det_ne_zero_of_full_rank_positive"),
                H("augmented det ne zero of full rank positive"),
                StatementSource.FromAuthor(Disp(Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("d"), Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("N")))), CloseBrace), Comma, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("M"), Sp, Colon, Sp, Call("Matrix"), Sp, Parenthesized(Seq(Call("Fin"), Sp, F.Id("d"))), Sp, Parenthesized(Seq(Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))))), Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(Call("Function"), Sp, Dot, Sp, Call("Injective"), Sp, Parenthesized(Seq(Call("fun"), Sp, F.Id("z"), Sp, Colon, Sp, Call("Fin"), Sp, F.Id("d"), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))), Sp, Mapsto, Sp, F.Id("M"), Sp, Dot, Sp, Call("transpose"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, F.Id("z"))))), Sp, To, Sp, Seq(Forall, Sp, Parenthesized(Seq(F.Id("x"), Sp, Colon, Sp, Call("Fin"), Sp, Parenthesized(Seq(F.Id("d"), Sp, Plus, Sp, D(1))), Sp, To, Sp, Seq(Mathbb, Grp(F.Id("Z"))))), Comma, Sp, Seq(Parenthesized(Seq(F.Id("M"), Sp, new Formula.Subscript(Star, F.Id("v")), Sp, F.Id("x"), Sp, Eq, Sp, D(0))), Sp, To, Sp, Seq(Parenthesized(Seq(Sum, Sp, F.Id("j"), Sp, Comma, Sp, F.Id("x"), Sp, F.Id("j"), Sp, Neq, Sp, D(0))), Sp, To, Sp, Seq(Parenthesized(Seq(Call("augment"), Sp, F.Id("M"))), Sp, Dot, Sp, Call("det"), Sp, Neq, Sp, D(0)))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Rounded partial weights encode a minimal nonnegative kernel vector in a finite cube."))),
                DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Call(string name) => Seq(Operatorname, Grp(F.Id(name)));
}
