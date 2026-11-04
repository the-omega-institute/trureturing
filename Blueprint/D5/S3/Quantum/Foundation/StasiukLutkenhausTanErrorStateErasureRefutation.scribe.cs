using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Foundation;

internal sealed class StasiukLutkenhausTanErrorStateErasureRefutationDocument : IScribeDocumentDefinition
{
    private const string Owner = "D5/S3/Quantum/Foundation/StasiukLutkenhausTanErrorStateErasureRefutation.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/stasiuklutkenhaustan2025erasure");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A rational qubit ensemble prevents exact error erasure while preserving both correct states.",
        H("The operational error-state erasure conjecture is false"),
        Blocks(
            Paragraph(Text(
                "The classical fair public bit is part of both the input and output of a single completely positive trace-preserving channel. The channel may act coherently on the entire joint system. DensityState and QuantumChannel refer to FiniteStateChannel.")),
            Describe.Lean(
                DescribeId.Create("rho-et"), DeclarationHandle.Create(Owner + "rhoET"),
                H("The conditional state with its public bit"),
                StatementSource.FromAuthor(Disp(RhoFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Equation (6), p. 2, defines the conditional ET state by the sum of the two orthogonal flag blocks with equal weights.")),
                    Paragraph(Text(
                        "The Bool values false and true represent 0 and 1; Bool.not complements a bit. Row i and column j have Eve coordinate in their first component and public-bit coordinate in their second. Each flag block has weight one half; the second block complements both outcome bits. The displayed equality specifies every matrix entry."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("erases-errors-preserving-correct"),
                DeclarationHandle.Create(Owner + "ErasesErrorsPreservingCorrect"),
                H("One channel with three simultaneous requirements"),
                StatementSource.FromAuthor(Disp(ErasureFormula())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(SourceQuote(),
                    Paragraph(Text(
                        "This predicate requires the channel to preserve the 00 and 11 matrices separately and to send the 01 and 10 matrices to the same output. It imposes all three equalities on one channel."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("claim"), DeclarationHandle.Create(Owner + "claim"),
                H("The universal operational assertion"),
                StatementSource.FromAuthor(Disp(new Formula.Logic(F.Id("claim"),
                    FormulaLogicOperator.Iff, ClaimBody()))),
                AssessedProvenance.FromLiterature(Source),
                Blocks(SourceQuote(),
                    Paragraph(Text(
                        "The dimension d ranges over all natural numbers, and sigma ranges over four normalized conditional density states. The same output dimension and the full public Bool register are retained. The assertion concerns a local operation on the given side-information; replacing the underlying attack is a separate question."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("result"), DeclarationHandle.Create(Owner + "result"),
                H("A two-dimensional counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use rank-one projectors of (1,0), (9999/10001,200/10001), (29197/50005,40596/50005), and (3/5,4/5), in 00,01,10,11 order. Their public-bit extensions are positive matrices of trace one. The correct-state trace distance is 4/5, and each same-Alice-bit correct-to-error distance is 200/10001.")),
                    Paragraph(Text(
                        "For every joint channel, trace-distance contraction on the two short legs and the triangle inequality force the sum of the two correct-state disturbances and the residual error-output distance to be at least 38004/50005. Exact preservation and exact erasure would make all three terms zero.")),
                    Paragraph(Text(
                        "If the error outputs coincide, the two correct-state disturbances must sum to at least 38004/50005. Theorem 2, which assumes equal error states, is not refuted. A weaker replacement-attack assertion and positive asymptotic key rates remain separate questions.")),
                    Paragraph(Text(
                        "The physical preparation has balanced positive key-event probabilities, distinct flagged states, CHSH violation and Q=9/25<9/16. These physical and Chernoff calculations are additional to the matrix-state refutation.")),
                    Paragraph(Text(
                        "Bhavsar, Moon and Bae, arXiv:2602.05870v2, address neighbouring asymptotic key-rate conditions. Finite-blocklength security, the replacement-realization question, optimality of the disturbance constant and positive erasure with an orthogonal correct/error record remain open here."))),
                DescribeRole.Theorem))));

    private static DocumentBlock SourceQuote() => Paragraph(
        Text("We remark that it does seem plausible to conjecture that Eve can indeed always perform an operation on her side-information such that this condition is fulfilled (while keeping the states "),
        Math(Seq(new Formula.Subscript(Rho, Seq(F.Id("ET"), Vert, D(0, 0))), Comma,
            new Formula.Subscript(Rho, Seq(F.Id("ET"), Vert, D(1, 1))))),
        Text(" unchanged), because it essentially corresponds to having Eve “erase” her side-information whenever Alice and Bob did not get the same output value. (Section III A, p. 5, immediately after Theorem 2.)"));

    private static Formula RhoFormula()
    {
        Formula i = F.Id("i"), j = F.Id("j"), a = F.Id("a"), b = F.Id("b");
        Formula entry = If(Proj(i, 2),
            App(Call("val", App(F.Id("sigma"), App(Q("Bool", "not"), a), App(Q("Bool", "not"), b))), Proj(i, 1), Proj(j, 1)),
            App(Call("val", App(F.Id("sigma"), a, b)), Proj(i, 1), Proj(j, 1)));
        Formula body = If(Equal(Proj(i, 2), Proj(j, 2)),
            Multiply(Parenthesized(Seq(new Formula.Fraction(D(1), D(2)), Colon, Complexes())), Parenthesized(entry)), D(0));
        return Parameters(All([Bound("a", F.Id("Bool")), Bound("b", F.Id("Bool")),
            Bound("i", Joint()), Bound("j", Joint())],
            Equal(App(Call("rhoET", F.Id("sigma"), a, b), i, j), body)));
    }

    private static Formula ErasureFormula() => Parameters(All([Bound("channel", Channels())],
        new Formula.Logic(Call("ErasesErrorsPreservingCorrect", F.Id("sigma"), F.Id("channel")),
            FormulaLogicOperator.Iff, ErasureBody())));

    private static Formula ErasureBody()
    {
        Formula r00 = Raw("false", "false"), r11 = Raw("true", "true");
        Formula r01 = Raw("false", "true"), r10 = Raw("true", "false");
        return new Formula.Logic(Equal(Channel(r00), r00), FormulaLogicOperator.And,
            new Formula.Logic(Equal(Channel(r11), r11), FormulaLogicOperator.And,
                Equal(Channel(r01), Channel(r10))));
    }

    private static Formula ClaimBody() => Parameters(new Formula.BindMany(FormulaQuantifier.Exists,
        [Bound("channel", Channels())],
        Call("ErasesErrorsPreservingCorrect", F.Id("sigma"), F.Id("channel"))));
    private static Formula Raw(string a, string b) => App(Q("CStarMatrix", "ofMatrix"),
        Call("rhoET", F.Id("sigma"), F.Id(a), F.Id(b)));
    private static Formula Channel(Formula x) => App(Call("toCompletelyPositiveMap", F.Id("channel")), x);
    private static Formula Parameters(Formula body) => All([Bound("d", Naturals()),
        Bound("sigma", new Formula.TypeArrow(F.Id("Bool"), new Formula.TypeArrow(F.Id("Bool"),
            Call("DensityState", Call("Fin", F.Id("d"))))))], body);
    private static Formula Joint() => Seq(Call("Fin", F.Id("d")), Sp, Times, Sp, F.Id("Bool"));
    private static Formula Channels() => Call("QuantumChannel", Parenthesized(Joint()), Parenthesized(Joint()));
    private static Formula Naturals() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complexes() => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Proj(Formula x, byte n) => Seq(x, Dot, D(n));
    private static Formula App(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Q(params string[] parts) => Seq(Operatorname,
        Grp(Seq(parts.SelectMany((part, index) => index == 0
            ? new[] { F.Id(part) } : new[] { Dot, F.Id(part) }).ToArray())));
    private static Formula If(Formula test, Formula yes, Formula no) => Seq(
        F.Text, Grp(F.Id("if")), Sp, Parenthesized(test), Sp,
        F.Text, Grp(F.Id("then")), Sp, Parenthesized(yes), Sp,
        F.Text, Grp(F.Id("else")), Sp, Parenthesized(no));
    private static Formula Parenthesized(Formula x) => Seq(Open, x, Close);
    private static Formula.BoundVariable Bound(string name, Formula type) => new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula.BoundVariable[] variables, Formula body) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
}
