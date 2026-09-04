using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.PrimeForms;

internal sealed class PrimaryPseudoperfectPortCompositionDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/PrimeForms/PrimaryPseudoperfectPortComposition.";

    private static readonly LibraryNoteRef Wang =
        LibraryNoteRef.Create("D5/L/Arith/wang2026port");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The complementary-prime-divisor sum has a coprime Leibniz rule, which drives "
            + "port composition and the coprime extension criterion for primary "
            + "pseudoperfect numbers.",
        H("Primary Pseudoperfect Port Composition"),
        Blocks(
            Paragraph(Text(
                "For natural numbers R, c, and B, portDelta(R,c,B) is the truncated "
                    + "natural difference cB - R squarefreeDeriv(B). The theorems below "
                    + "use the squarefreeDeriv and IsPPN definitions from the frozen "
                    + "PrimaryPseudoperfectPorts module.")),
            Describe.Lean(
                DescribeId.Create("coprime-leibniz-rule"),
                DeclarationHandle.Create(Prefix + "squarefreeDeriv_mul"),
                H("Coprime Leibniz rule"),
                StatementSource.FromAuthor(LeibnizRule()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Coprimality partitions the prime factors of AB into disjoint factors "
                        + "from A and B. Transporting each complementary divisor across "
                        + "that partition produces the two summands."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("port-composition-law"),
                DeclarationHandle.Create(Prefix + "portDelta_mul"),
                H("Port composition law"),
                StatementSource.FromAuthor(PortComposition()),
                AssessedProvenance.FromRepo(Wang),
                Blocks(
                    Paragraph(Text(
                        "On coprime factors, the Leibniz rule makes the residual through "
                            + "AB equal to the residual obtained by substituting the output "
                            + "at A as the input coefficient at B.")),
                    Paragraph(Text(
                        "Wang's Lemma 6.2 states this orientation and its symmetric partner "
                            + "for coprime squarefree integers. The Lean theorem is classified "
                            + "as repository-derived with that acknowledgement because it "
                            + "drops both squarefreeness hypotheses and records one orientation."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("coprime-extension-criterion"),
                DeclarationHandle.Create(Prefix + "isPPN_mul_iff_port"),
                H("Coprime extension criterion"),
                StatementSource.FromAuthor(CoprimeExtension()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "If K is primary pseudoperfect and C is a nontrivial squarefree factor "
                        + "coprime to K, then KC is primary pseudoperfect exactly when the "
                        + "natural residual C - K squarefreeDeriv(C) equals one."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Deriv(Formula value) => Call("squarefreeDeriv", value);

    private static Formula Ppn(Formula value) => Call("IsPPN", value);

    private static Formula Squarefree(Formula value) => Call("Squarefree", value);

    private static Formula Coprime(Formula left, Formula right) =>
        Call("Coprime", left, right);

    private static Formula IffFormula(Formula left, Formula right) =>
        Seq(Open, left, Sp, Leftrightarrow, Sp, right, Close);

    private static Formula AndFormula(params Formula[] clauses)
    {
        var items = new List<Formula>();
        for (var i = 0; i < clauses.Length; i++)
        {
            if (i > 0) items.AddRange([Sp, Land, Sp]);
            items.Add(clauses[i]);
        }
        return Seq([.. items]);
    }

    private static Formula LeibnizRule()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Coprime(a, b), Sp, Rightarrow, Sp,
            Equal(
                Deriv(Multiply(a, b)),
                Add(Multiply(a, Deriv(b)), Multiply(b, Deriv(a)))), Dot));
    }

    private static Formula PortComposition()
    {
        Formula a = F.Id("A");
        Formula b = F.Id("B");
        Formula r = F.Id("R");
        Formula c = F.Id("c");
        return Disp(Seq(
            Forall, Sp, a, Comma, Sp, b, Comma, Sp, r, Comma, Sp, c,
            Sp, InMacro, Sp, Naturals(), Comma, Sp,
            Coprime(a, b), Sp, Rightarrow, Sp,
            Equal(
                Call("portDelta", r, c, Multiply(a, b)),
                Call("portDelta", Multiply(r, a), Call("portDelta", r, c, a), b)), Dot));
    }

    private static Formula CoprimeExtension()
    {
        Formula k = F.Id("K");
        Formula c = F.Id("C");
        Formula hypotheses = AndFormula(
            Ppn(k), Squarefree(c), Seq(D(1), Sp, Lt, Sp, c), Coprime(k, c));
        Formula conclusion = IffFormula(
            Ppn(Multiply(k, c)),
            Equal(Subtract(c, Multiply(k, Deriv(c))), Num(1)));
        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, c, Sp, InMacro, Sp, Naturals(), Comma, Sp,
            hypotheses, Sp, Rightarrow, Sp, conclusion, Dot));
    }
}
