using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Entropy;

internal sealed class ChargeSectorMajorizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Entropy/ChargeSectorMajorizationRefutation";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Entropy/ariasdigiuliokeskivakkuritonni2023capacity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Normalization inside a common charge sector can reverse a majorization order.",
        H("Charge-sector normalization refutes majorization preservation"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("charge-sector-majorization-sector-spectrum"),
                DeclarationHandle.Create(Module + ".sectorSpectrum"),
                H("The normalized charge-sector spectrum"),
                StatementSource.FromAuthor(Disp(SectorSpectrumDefinition())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For a real weight vector r on Fin n and an integer charge function, "
                        + "sectorSpectrum selects the indices with charge q, divides each selected "
                        + "weight by the total weight in that sector, and sorts the resulting list "
                        + "in descending order. This is the normalized charge-block spectrum used "
                        + "in the source's charge decomposition (arXiv:2301.02117v1, lines 3550–3569)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charge-sector-majorization-claim"),
                DeclarationHandle.Create(Module + ".claim"),
                H("Majorization preservation in every positive sector"),
                StatementSource.FromAuthor(Disp(ClaimDefinition())),
                AssessedProvenance.FromRepo(Source),
                Blocks(Paragraph(Text(
                    "The claim asks whether majorization of two normalized nonnegative weight "
                        + "vectors forces majorization of their normalized spectra in every charge "
                        + "sector having positive weight in both vectors. It is the finite diagonal "
                        + "formal reading of the question left open in Section 7 of the source "
                        + "(arXiv:2301.02117v1, line 4140)."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("charge-sector-majorization-result"),
                DeclarationHandle.Create(Module + ".result"),
                H("A four-level counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(Parenthesized(F.Id("claim"))))),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text(
                        "Use four levels with charge vector (0,0,1,1), r=(6/20,6/20,7/20,1/20), "
                            + "and s=(7/20,5/20,4/20,4/20). Each vector is nonnegative and sums "
                            + "to one. Their descending spectra are (7,6,6,1)/20 and "
                            + "(7,5,4,4)/20, so the prefix sums establish Majorizes(desc r, desc s).")),
                    Paragraph(Text(
                        "In charge sector zero both total weights are 3/5. The normalized spectra "
                            + "are therefore (1/2,1/2) and (7/12,5/12). The first prefix inequality "
                            + "required for Majorizes in the proposed direction would be "
                            + "1/2 ≥ 7/12, which is false. Thus the positive-sector hypotheses "
                            + "hold while the sector majorization conclusion fails, proving ¬claim."))),
                DescribeRole.Theorem,
                new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("arias-di-giulio-keski-vakkuri-tonni-2023-charge-sector-majorization"),
                    ResolutionKind.Refuted)))));

    private static Formula SectorSpectrumDefinition()
    {
        Formula n = F.Id("n"), r = F.Id("r"), charge = F.Id("charge"), q = F.Id("q");
        Formula i = F.Id("i"), a = F.Id("a"), b = F.Id("b");
        Formula finN = Fin(n), real = Reals(), integer = Integers();
        Formula filtered = At(Qualified("List", "filter"),
            Lambda("i", finN, At(F.Id("decide"), Eq(At(charge, i), q))),
            At(Qualified("List", "finRange"), n));
        Formula mapped = At(Qualified("List", "map"),
            Lambda("i", finN, Div(At(r, i), At(F.Id("pushforward"), charge, r, q))),
            filtered);
        Formula comparator = Lambda("a", real,
            Lambda("b", real, At(F.Id("decide"), Le(b, a))));
        Formula body = Eq(
            At(F.Id("sectorSpectrum"), r, charge, q),
            At(Qualified("List", "mergeSort"), mapped, comparator));
        return ImplicitAll("n", Nat(),
            All("r", new Formula.TypeArrow(finN, real),
                All("charge", new Formula.TypeArrow(finN, integer),
                    All("q", integer, body))));
    }

    private static Formula ClaimDefinition()
    {
        Formula n = F.Id("n"), charge = F.Id("charge"), r = F.Id("r"), s = F.Id("s");
        Formula finN = Fin(n), real = Reals(), integer = Integers();
        Formula nonnegativeR = All("i", finN, Le(Zero(real), At(r, F.Id("i"))));
        Formula massR = Eq(SumOver("i", finN, At(r, F.Id("i"))), One(real));
        Formula nonnegativeS = All("i", finN, Le(Zero(real), At(s, F.Id("i"))));
        Formula massS = Eq(SumOver("i", finN, At(s, F.Id("i"))), One(real));
        Formula global = At(F.Id("Majorizes"), At(F.Id("desc"), r), At(F.Id("desc"), s));
        Formula q = F.Id("q");
        Formula sector = At(F.Id("Majorizes"),
            At(F.Id("sectorSpectrum"), r, charge, q),
            At(F.Id("sectorSpectrum"), s, charge, q));
        Formula positiveR = Lt(Zero(real), At(F.Id("pushforward"), charge, r, q));
        Formula positiveS = Lt(Zero(real), At(F.Id("pushforward"), charge, s, q));
        Formula sectorClause = All("q", integer, Imp(positiveR, Imp(positiveS, sector)));
        Formula body = All("n", Nat(),
            All("charge", new Formula.TypeArrow(finN, integer),
                All("r", new Formula.TypeArrow(finN, real),
                    All("s", new Formula.TypeArrow(finN, real),
                        Imp(nonnegativeR,
                            Imp(massR,
                                Imp(nonnegativeS,
                                    Imp(massS,
                                        Imp(global, sectorClause)))))))));
        return Eq(F.Id("claim"), Parenthesized(body));
    }

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Reals() => Seq(Mathbb, Grp(F.Id("R")));
    private static Formula Integers() => Seq(Mathbb, Grp(F.Id("Z")));
    private static Formula Fin(Formula n) => At(Qualified("Fin"), n);
    private static Formula At(Formula function, params Formula[] arguments) =>
        new Formula.Apply(function, [.. arguments]);
    private static Formula Qualified(params string[] parts)
    {
        var items = new System.Collections.Generic.List<Formula>();
        foreach (var part in parts)
        {
            if (items.Count > 0)
            {
                items.Add(Dot);
            }

            items.Add(F.Id(part));
        }

        return Seq(Operatorname, Grp(Seq([.. items])));
    }

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Typed(Formula value, Formula type) =>
        Parenthesized(Seq(value, Colon, Sp, type));
    private static Formula Zero(Formula type) => Typed(D(0), type);
    private static Formula One(Formula type) => Typed(D(1), type);
    private static Formula Lambda(string name, Formula type, Formula body) =>
        Parenthesized(Seq(LambdaLower, Sp, Typed(F.Id(name), type), Sp, Mapsto, Sp,
            Parenthesized(body)));
    private static Formula All(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, Typed(F.Id(name), type), Comma, Sp, Parenthesized(body));
    private static Formula Imp(Formula premise, Formula conclusion) =>
        new Formula.Logic(Parenthesized(premise), FormulaLogicOperator.Implies,
            Parenthesized(conclusion));
    private static Formula Eq(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.Equal, right);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Lt(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThan, right);
    private static Formula Div(Formula numerator, Formula denominator) =>
        new Formula.Fraction(numerator, denominator);
    private static Formula SumOver(string name, Formula type, Formula body) =>
        Seq(new Formula.Subscript(Sum, Seq(F.Id(name), Colon, Sp, type)), Sp,
            Parenthesized(body));
    private static Formula ImplicitAll(string name, Formula type, Formula body) =>
        Seq(Forall, Sp, OpenBrace, F.Id(name), Colon, Sp, type, CloseBrace, Comma, Sp,
            Parenthesized(body));
}
