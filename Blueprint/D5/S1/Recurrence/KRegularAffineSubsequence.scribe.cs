using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence;

internal sealed class KRegularAffineSubsequenceDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/KRegularAffineSubsequence.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceComposition/alloucheshallit1992regular");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every positive-step affine subsequence of an integer k-regular sequence is k-regular.",
        H("Affine subsequences of integer k-regular sequences"),
        Blocks(
            Paragraph(Text(
                "Sequences have domain the natural numbers, including zero, and values in the integers. "
                + "Write K_k(s) for the set of all sequences n ↦ s(k^e n+r), where e and r are natural "
                + "numbers and r<k^e. The sequence s is k-regular exactly when the integer span of "
                + "K_k(s) is finitely generated; denote this property by Regular(k,s). "
                + "Neither the values nor the kernel are required to be finite.")),
            Node("affine_kernel_span_le", "Uniform transport of kernel spans", TransportFormula(),
                "For every base k≥2, positive natural step a, natural offset b, and finite family G "
                + "whose integer span equals the span of K_k(s), the entire sampled kernel span lies "
                + "in the span of the displayed family. To see this, fix any e and r with r<k^e and "
                + "write ar+b=c k^e+d with d<k^e. Then c<a+b and "
                + "s(a(k^e n+r)+b)=s(k^e(an+c)+d). The sequence m ↦ s(k^e m+d) belongs to K_k(s) "
                + "and hence to the integer span of G. Substitution m=an+c is linear, so the sampled "
                + "kernel element belongs to the span of n ↦ g(an+c), g∈G. The same fixed family, "
                + "with all c<a+b, works for every e and r. This is the containment used in the proof "
                + "of Allouche and Shallit's preprint Theorem 2.6, PDF page 7."),
            Node("is_k_regular_affine_subsequence", "Affine-subsequence closure", ClosureFormula(),
                "For every k≥2, every natural a≥1 and b, and every integer-valued k-regular sequence s, "
                + "the sequence n ↦ s(an+b) is k-regular in the same base. Extract a finite generating "
                + "family G for the original kernel span. The family of affine observations above is "
                + "finite, being the image of G times the natural offsets c<a+b. The uniform containment "
                + "places the sampled kernel span inside its finitely generated integer span. Since "
                + "the integers form a Noetherian ring, that submodule is finitely generated. This is "
                + "the integer-coefficient case of the cited preprint theorem; its coefficient convention "
                + "and regularity definition appear on PDF page 3. The offset is nonnegative because "
                + "it is natural. No finite-range, finite-kernel, periodicity, recurrence, or base-two "
                + "hypothesis occurs. The mathematical assertion ranges over every base k≥2; its "
                + "integer-valued sequence space is the one fixed here."))));

    private static DocumentBlock Node(string name, string title, Formula formula, string prose) =>
        Describe.Lean(DescribeId.Create("k-regular-affine-" + name.Replace('_', '-')),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula TransportFormula()
    {
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var s = F.Id("s");
        var g = F.Id("g");
        var c = F.Id("c");
        var f = F.Id("f");
        var family = F.Id("G");
        var observed = LambdaIn("n", Naturals(), Call("s", Add(Multiply(a, F.Id("n")), b)));
        var observation = LambdaIn("n", Naturals(), Call("g", Add(Multiply(a, F.Id("n")), c)));
        var member = Some("g", SequenceType(), And(Member(g, family),
            Some("c", Naturals(), And(Less(c, Add(a, b)), Equal(f, observation)))));
        var generators = Seq(OpenBrace, f, Colon, Sp, SequenceType(), Sp, Mid, Sp, member, Sp, CloseBrace);
        var conclusion = Subset(Span(Kernel(k, observed)), Span(generators));
        var spanning = Equal(Span(family), Span(Kernel(k, s)));
        var generated = All("G", Call("Finset", SequenceType()), Implies(spanning, conclusion));
        var hypotheses = Implies(LessOrEqual(D(2), k), Implies(LessOrEqual(D(1), a), generated));
        return Disp(All("k", Naturals(), All("a", Naturals(), All("b", Naturals(),
            All("s", SequenceType(), hypotheses)))));
    }

    private static Formula ClosureFormula()
    {
        var k = F.Id("k");
        var a = F.Id("a");
        var b = F.Id("b");
        var s = F.Id("s");
        var observed = LambdaIn("n", Naturals(), Call("s", Add(Multiply(a, F.Id("n")), b)));
        return Disp(All("k", Naturals(), All("a", Naturals(), All("b", Naturals(),
            All("s", SequenceType(), Implies(LessOrEqual(D(2), k), Implies(LessOrEqual(D(1), a),
                Implies(Call("Regular", k, s), Call("Regular", k, observed)))))))));
    }

    private static Formula Naturals() => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula Integers() => new Formula.Integers();
    private static Formula SequenceType() => Seq(Open, Naturals(), Sp, To, Sp, Integers(), Close);
    private static Formula Span(Formula set) => Seq(
        Operatorname, Grp(F.Id("span")), Underscore, Grp(Integers()), Open, set, Close);
    private static Formula Kernel(Formula k, Formula s) => Seq(
        F.Id("K"), Underscore, Grp(k), Open, s, Close);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula And(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.And, right);
    private static Formula Implies(Formula left, Formula right) => new Formula.Logic(left, FormulaLogicOperator.Implies, right);
    private static Formula Equal(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Less(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula LessOrEqual(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula left, Formula right) => new Formula.Relation(left, FormulaRelationOperator.MemberOf, right);
    private static Formula Subset(Formula left, Formula right) => Seq(left, Sp, Subseteq, Sp, right);
    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);
    private static Formula Some(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), domain, body);
    private static Formula LambdaIn(string variable, Formula domain, Formula body) => Seq(
        Open, F.Id(variable), Colon, Sp, domain, Sp, Mapsto, Sp, body, Close);
}
