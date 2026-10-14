using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class EvenLeggedHyperlinkReconstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Information/EvenLeggedHyperlinkReconstruction.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/santalla2026hyperlink");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Universal rational leg factors reconstruct every real complement-symmetric set function vanishing at the empty set from its nonempty even hyperlinks.",
        H("Reconstruction from even-legged hyperlinks"),
        Blocks(
            Node("hyperlink", "The signed subset transform", "hyperlink", HyperlinkFormula(),
                "Equation (5) defines the hyperlink by inclusion-exclusion over all subsets of I. The exponent is the natural-number difference between the two cardinalities, and the sign and set-function values are real. No symmetry or vanishing hypothesis is needed for this definition.",
                AssessedProvenance.FromLiterature(Source)),
            Node("leg-inverse-coeff", "The triangular inverse coefficients", "legInverseCoeff", InverseCoefficientFormula(),
                "The coefficient at rank zero is one. Odd ranks have coefficient zero. At a positive even rank r, the coefficient is minus one half of the sum over j : Fin r, whose summand is Nat.choose r val(j) times the coefficient at val(j) when val(j) is even, and zero otherwise. Here val(j) is the natural value of j : Fin r. Each binomial coefficient is cast to the rational numbers before multiplication. This recurrence determines a rational sequence by strong recursion.",
                AssessedProvenance.FromRepo()),
            Node("leg-factor", "The rational leg factors", "legFactor", LegFactorFormula(),
                "For p at most m, the sum ranges over even k between two and m, inclusive. The binomial difference counts the k-element subsets of an m-element set meeting both sides of a split into p and m minus p elements. Each binomial coefficient is cast to the rational numbers before subtraction. Both m minus k and m minus p use natural-number subtraction. The value is zero when p exceeds m.",
                AssessedProvenance.FromRepo()),
            Node("claim", "A single coefficient family for every finite system", "claim", ClaimFormula(),
                "Appendix B, (B2), proposes reconstruction using even-legged hyperlinks with leg factors independent of the number of parties. The coefficient existential precedes N and S: one rational family works for every N and every real complement-symmetric set function vanishing at the empty set. The two coefficient laws give zero values at both ends and symmetry under p mapping to m minus p, for all natural m and p. The sum includes precisely the nonempty even subsets of Fin N. Entanglement entropies of a finite-dimensional pure state have the two set-function properties: complementary reduced states have the same nonzero spectrum, and the empty block has entropy zero. This identification is mathematical background and is not part of the formal statement.",
                AssessedProvenance.FromLiterature(Source)),
            Describe.Lean(
                DescribeId.Create("even-hyperlink-result"), DeclarationHandle.Create(Prefix + "result"),
                H("The rational leg factors give the reconstruction"),
                StatementSource.FromAuthor(Disp(Local("claim"))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "The theorem concerns every real complement-symmetric set function vanishing at the empty set. The explicit coefficient family is legFactor. Möbius inversion on subsets recovers the set function from all its hyperlinks. The complement transform expresses each hyperlink of the complemented function as its parity sign times the sum over containing subsets. Descending induction then shows that the nonempty even hyperlinks, together with the empty value, uniquely determine a complement-symmetric set function.")),
                    Paragraph(Text(
                        "For each nonempty even subset K, the auxiliary family q_K has value minus one half when K meets both A and its complement, and zero otherwise. Its even hyperlinks give a triangular system over containing subsets. The recurrence defining legInverseCoeff inverts this system. The resulting linear combination of the q_K has the same even hyperlinks as the original function, so uniqueness identifies the two functions. Counting the subsets of each I that cross the split between A and its complement gives legFactor at the cardinalities of I and its intersection with A. This proves the reconstruction in (B2) for every finite N, along with the zero and symmetry laws."))),
                DescribeRole.Theorem,
                openProblemResolutionClaim: new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("santalla-singha-roy-sierra-rodriguez-laguna-2026-even-legged-reconstruction"),
                    ResolutionKind.Proved))
        )));

    private static DocumentBlock Node(string id, string title, string declaration, Formula formula,
        string prose, AssessedProvenance provenance) => Describe.Lean(
            DescribeId.Create("even-hyperlink-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(formula)), provenance,
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula X(string name) => F.Id(name);
    private static Formula Qualified(params string[] names)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var name in names)
        {
            if (items.Count > 0) items.Add(Dot);
            items.Add(X(name));
        }
        return Seq(Operatorname, Grp(Seq([.. items])));
    }
    private static Formula Local(string name) =>
        Qualified("D5", "S3", "Quantum", "Information", "EvenLeggedHyperlinkReconstruction", name);
    private static Formula At(Formula function, params Formula[] args) => new Formula.Apply(function, [.. args]);
    private static Formula LocalCall(string name, params Formula[] args) => At(Local(name), args);
    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) => Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Naturals() => Seq(Mathbb, Grp(X("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(X("R")));
    private static Formula Rationals() => Seq(Mathbb, Grp(X("Q")));
    private static Formula FinsetOf(Formula type) => At(Qualified("Finset"), type);
    private static Formula FinOfN() => At(Qualified("Fin"), X("N"));
    private static Formula FunctionTo(Formula domain, Formula codomain) =>
        Parenthesized(new Formula.TypeArrow(domain, codomain));
    private static Formula All(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), type, body);
    private static Formula Some(string variable, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(variable), type, body);
    private static Formula Equal(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula NotEqual(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.NotEqual, right);
    private static Formula AtMost(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Member(Formula element, Formula set) =>
        new Formula.Relation(element, FormulaRelationOperator.MemberOf, set);
    private static Formula And(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.And, Parenthesized(right));
    private static Formula Implies(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Implies, Parenthesized(right));
    private static Formula Equivalent(Formula left, Formula right) =>
        new Formula.Logic(Parenthesized(left), FormulaLogicOperator.Iff, Parenthesized(right));
    private static Formula Add(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Add, right);
    private static Formula Subtract(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Subtract, right);
    private static Formula Multiply(Formula left, Formula right) => new Formula.Binary(left, FormulaBinaryOperator.Multiply, right);
    private static Formula NatSubtract(Formula left, Formula right) => Typed(Subtract(left, right), Naturals());
    private static Formula Card(Formula set) => At(Qualified("Finset", "card"), set);
    private static Formula Powerset(Formula set) => At(Qualified("Finset", "powerset"), set);
    private static Formula EvenRank(Formula rank) => At(Qualified("Even"), rank);
    private static Formula Complement(Formula set) => At(Qualified("Finset", "compl"), set);
    private static Formula ChooseRational(Formula n, Formula k) => Typed(At(Qualified("Nat", "choose"), n, k), Rationals());
    private static Formula MinusHalf() => new Formula.Negate(Typed(new Formula.Fraction(D(1), D(2)), Rationals()));
    private static Formula IfThenElse(Formula condition, Formula yes, Formula no) => Parenthesized(Seq(
        F.Text, Grp(X("if")), Sp, condition, Sp, F.Text, Grp(X("then")), Sp, yes,
        Sp, F.Text, Grp(X("else")), Sp, no));
    private static Formula SumOver(string variable, Formula set, Formula summand) => Seq(
        new Formula.Subscript(Sum, Member(X(variable), set)), Sp, Parenthesized(summand));
    private static Formula SumWhere(string variable, Formula set, Formula condition, Formula summand) => Seq(
        new Formula.Subscript(Sum, Seq(Member(X(variable), set), Comma, Sp, condition)),
        Sp, Parenthesized(summand));

    private static Formula HyperlinkFormula()
    {
        Formula setType = FinsetOf(X("alpha"));
        Formula exponent = NatSubtract(Card(X("I")), Card(X("B")));
        Formula sign = new Formula.Power(Typed(new Formula.Negate(D(1)), Reals()), exponent);
        Formula sum = SumOver("B", Powerset(X("I")), Multiply(sign, At(X("S"), X("B"))));
        return All("alpha", Qualified("Type"), All("S", FunctionTo(setType, Reals()),
            All("I", setType, Equal(LocalCall("hyperlink", X("S"), X("I")), sum))));
    }

    private static Formula InverseCoefficientFormula()
    {
        Formula jval = Call("val", X("j"));
        Formula sum = Seq(new Formula.Subscript(Sum, Seq(X("j"), Colon, Sp, At(Qualified("Fin"), X("r")))),
            Sp, Parenthesized(IfThenElse(EvenRank(jval),
                Multiply(ChooseRational(X("r"), jval), LocalCall("legInverseCoeff", jval)), D(0))));
        return All("r", Naturals(), Equal(LocalCall("legInverseCoeff", X("r")),
            IfThenElse(Equal(X("r"), D(0)), D(1),
                IfThenElse(EvenRank(X("r")), Multiply(MinusHalf(), sum), D(0)))));
    }

    private static Formula LegFactorFormula()
    {
        Formula binomialDifference = Subtract(
            Subtract(ChooseRational(X("m"), X("k")), ChooseRational(X("p"), X("k"))),
            ChooseRational(NatSubtract(X("m"), X("p")), X("k")));
        Formula sum = SumWhere("k", At(Qualified("Finset", "range"), Add(X("m"), D(1))),
            And(AtMost(D(2), X("k")), EvenRank(X("k"))),
            Multiply(LocalCall("legInverseCoeff", NatSubtract(X("m"), X("k"))),
                Parenthesized(binomialDifference)));
        return All("m", Naturals(), All("p", Naturals(), Equal(LocalCall("legFactor", X("m"), X("p")),
            IfThenElse(AtMost(X("p"), X("m")), Multiply(MinusHalf(), sum), D(0)))));
    }

    private static Formula ClaimFormula()
    {
        Formula setType = FinsetOf(FinOfN());
        Formula zeroLaws = All("m", Naturals(), And(
            Equal(At(X("L"), X("m"), D(0)), D(0)), Equal(At(X("L"), X("m"), X("m")), D(0))));
        Formula symmetryLaw = All("m", Naturals(), All("p", Naturals(), Equal(
            At(X("L"), X("m"), X("p")), At(X("L"), X("m"), NatSubtract(X("m"), X("p"))))));
        Formula complementLaw = All("A", setType, Equal(At(X("S"), Complement(X("A"))), At(X("S"), X("A"))));
        Formula intersection = At(Qualified("Finset", "inter"), X("I"), X("A"));
        Formula summand = Multiply(Typed(At(X("L"), Card(X("I")), Card(intersection)), Reals()),
            LocalCall("hyperlink", X("S"), X("I")));
        Formula sum = SumWhere("I", Powerset(Typed(Qualified("Finset", "univ"), setType)),
            And(EvenRank(Card(X("I"))), NotEqual(X("I"), Emptyset)), summand);
        Formula reconstruction = All("N", Naturals(), All("S", FunctionTo(setType, Reals()),
            Implies(Equal(At(X("S"), Emptyset), D(0)), Implies(complementLaw,
                All("A", setType, Equal(At(X("S"), X("A")), sum))))));
        return Equivalent(Local("claim"), Some("L", FunctionTo(Naturals(), FunctionTo(Naturals(), Rationals())),
            And(zeroLaws, And(symmetryLaw, reconstruction))));
    }
}
