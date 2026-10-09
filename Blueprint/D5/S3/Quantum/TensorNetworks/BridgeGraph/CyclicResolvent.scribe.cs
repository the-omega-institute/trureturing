using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks.BridgeGraph;

internal sealed class CyclicResolventDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/TensorNetworks/BridgeGraph/CyclicResolvent";
    private static Formula Parenthesized(Formula f) => Seq(Open, f, Close);
    private static Formula Qualified(params Formula[] names) => Seq(Operatorname, Grp(names));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "CyclicResolvent supplies the width-three bridge max-flow proof.",
        H("CyclicResolvent"), Blocks(
            Paragraph(Text("Formulas retain the Lean parameter types and all hypotheses. HDiv.hDiv and HMod.hMod are displayed infix: on natural and integer carriers they mean the respective Lean integer division and remainder operations; on rational carriers division is field division. Coe.coe denotes the coercion determined by the displayed target type. Finite and dependent-pair constructors omit proof fields, which do not change their values. A dash in a match pattern is an anonymous wildcard. CoeFun.coe and CoeSort.coe retain coercions to functions and types. All dimensions use ℕ, all construction coefficients use ℚ, and max-flow uses ℂ.")),
            Describe.Lean(DescribeId.Create("gls-cyclicresolvent-inclusion"),
                DeclarationHandle.Create(Owner + ".inclusion"),
                H("inclusion"), StatementSource.FromAuthor(Disp(Statement0())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The defining expression fixes inclusion for the consumed CyclicResolvent construction."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("gls-cyclicresolvent-inclusion-injective"),
                DeclarationHandle.Create(Owner + ".inclusion_injective"),
                H("inclusion_injective"), StatementSource.FromAuthor(Disp(Statement1())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("inclusion_injective is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-cyclicresolvent-cyclic-resolvent-lemma"),
                DeclarationHandle.Create(Owner + ".cyclic_resolvent_lemma"),
                H("cyclic_resolvent_lemma"), StatementSource.FromAuthor(Disp(Statement2())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("cyclic_resolvent_lemma is used on the live proof path of the width-three bridge construction."))),
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("gls-cyclicresolvent-schur-rank"),
                DeclarationHandle.Create(Owner + ".schur_rank"),
                H("schur_rank"), StatementSource.FromAuthor(Disp(Statement3())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The cyclic resolvent is injective or surjective in the respective dimension ordering and has rank min(A*D,B*G). backward is the unweighted cyclic shift; forwardHalf carries the closing weight 1/2."))),
                DescribeRole.Theorem))));

    private static Formula Statement0() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("m"), Sp, Colon, Sp, F.Id("Type"))), Sp, Parenthesized(Seq(F.Id("n"),
        Sp, Colon, Sp, F.Id("Type"))), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("m")), CloseBracket),
        Sp, Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, F.Id("n"), Sp, To, Sp, F.Id("m"))), Sp, Comma, Sp,
        Qualified(F.Id("CyclicResolvent"), Dot, F.Id("inclusion")), Sp, F.Id("e"), Sp, Eq, Sp,
        Parenthesized(Seq(Qualified(F.Id("Matrix"), Dot, F.Id("submatrix")), Sp, D(1), Sp, F.Id("id"), Sp,
        F.Id("e"))));

    private static Formula Statement1() =>
        Seq(Forall, Sp, Seq(OpenBrace, Seq(F.Id("m"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBrace,
        Seq(F.Id("n"), Sp, Colon, Sp, F.Id("Type")), CloseBrace), Sp, Seq(OpenBracket, Seq(F.Id("Fintype"), Sp,
        F.Id("n")), CloseBracket), Sp, Seq(OpenBracket, Seq(F.Id("DecidableEq"), Sp, F.Id("m")), CloseBracket), Sp,
        Parenthesized(Seq(F.Id("e"), Sp, Colon, Sp, F.Id("n"), Sp, To, Sp, F.Id("m"))), Sp, Comma, Sp,
        Qualified(F.Id("Function"), Dot, F.Id("Injective")), Sp, F.Id("e"), Sp, To, Sp, Qualified(F.Id("Function"),
        Dot, F.Id("Injective")), Sp, Parenthesized(Seq(Qualified(F.Id("CyclicResolvent"), Dot, F.Id("inclusion")), Sp,
        F.Id("e"))), Sp, Dot, Sp, F.Id("mulVec"));

    private static Formula Statement2() =>
        Qualified(F.Id("FloorSelectorCycles"), Dot, F.Id("CyclicResolventLemma"));

    private static Formula Statement3() =>
        Seq(Forall, Sp, Parenthesized(Seq(F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, Colon, Sp,
        Seq(Mathbb, Grp(F.Id("N"))))), Sp, Comma, Sp, D(0), Sp, F.Lt, Sp, F.Id("B"), Sp, To, Sp, F.Id("B"), Sp, Leq,
        Sp, F.Id("A"), Sp, To, Sp, D(0), Sp, F.Lt, Sp, F.Id("D"), Sp, To, Sp, F.Id("D"), Sp, Leq, Sp, F.Id("G"), Sp,
        To, Sp, Forall, Sp, Parenthesized(Seq(Kappa, Sp, Colon, Sp, Seq(Mathbb, Grp(F.Id("Q"))))), Sp, Comma, Sp,
        D(0), Sp, F.Lt, Sp, Kappa, Sp, To, Sp, Parenthesized(Seq(Qualified(F.Id("FloorSelectorCycles"), Dot,
        F.Id("schurMap")), Sp, F.Id("A"), Sp, F.Id("B"), Sp, F.Id("G"), Sp, F.Id("D"), Sp, Kappa)), Sp, Dot, Sp,
        F.Id("rank"), Sp, Eq, Sp, F.Id("min"), Sp, Parenthesized(Seq(F.Id("A"), Sp, Cdot, Sp, F.Id("D"))), Sp,
        Parenthesized(Seq(F.Id("B"), Sp, Cdot, Sp, F.Id("G"))));

}
