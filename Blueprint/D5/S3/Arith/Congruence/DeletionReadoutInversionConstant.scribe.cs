using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Congruence;

internal sealed class DeletionReadoutInversionConstantDocument : IScribeDocumentDefinition
{
    private const string Module =
        "D5/S3/Arith/Congruence/DeletionReadoutInversionConstant.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Full-deletion readings determine every coordinate with an attained product constant.",
        H("Deletion Readout Inversion Constant"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("deletion-reading"),
                DeclarationHandle.Create(Module + "R"),
                H("Deletion reading"),
                StatementSource.FromAuthor(ReadingFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For each selected coordinate, the factor vanishes exactly when the "
                        + "configuration takes the deleted value. Thus the sum retains precisely "
                        + "the configurations avoiding every prescribed value in T."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("observation-norm"),
                DeclarationHandle.Create(Module + "obsNorm"),
                H("Observation norm"),
                StatementSource.FromAuthor(ObservationNormFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "The maximum ranges over every coordinate subset and every dependent tuple "
                        + "of deleted values. The lower bound on each alphabet size makes this "
                        + "finite indexing family nonempty."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("inversion-constant"),
                DeclarationHandle.Create(Module + "kappa"),
                H("Tensor inverse row sum"),
                StatementSource.FromAuthor(ConstantFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "Each factor is the absolute row sum of J divided by m_i minus one, "
                        + "minus the identity. Their product is the tensor inverse row sum."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("deletion-readout-inversion-constant"),
                DeclarationHandle.Create(Module + "deletion_readout_inversion_constant"),
                H("Sharp full-deletion inversion bound"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The coordinate matrix J minus I is inverted by J divided by m_i minus "
                            + "one, minus I. Tensoring these inverses reconstructs each coefficient "
                            + "from the full-deletion readings, and the absolute row sums factor.")),
                    Paragraph(Text(
                        "For the displayed vector w, each coordinate sum is m_i minus two and "
                            + "each deleted coordinate sum has absolute value m_i minus one. "
                            + "Consequently every reading factors coordinatewise, the full "
                            + "deletion reading attains the observation norm, and the coefficient "
                            + "at the distinguished tuple attains the inversion bound."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula Bound(Formula value, Formula type) =>
        Seq(value, Colon, Sp, type);

    private static Formula Arrow(Formula source, Formula target) =>
        Seq(Open, source, Close, Sp, To, Sp, target);

    private static Formula Subscript(Formula value, Formula index) =>
        Seq(value, Underscore, Grp(index));

    private static Formula Abs(Formula value) => Seq(Lvert, Sp, value, Sp, Rvert);

    private static Formula Nat() => Seq(Mathbb, Grp(F.Id("N")));

    private static Formula Real() => Seq(Mathbb, Grp(F.Id("R")));

    private static Formula FinR() => Call("Fin", F.Id("r"));

    private static Formula Alphabet() =>
        Seq(Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, FinR()), Sp,
            Call("Fin", Subscript(F.Id("m"), F.Id("i"))));

    private static Formula Reading(Formula subset, Formula deleted, Formula state) =>
        Call("R", subset, deleted, state);

    private static Formula Indicator(Formula configuration, Formula deleted) =>
        Seq(Mathbf, Sp, Grp(D(1)), Underscore, Grp(
            Subscript(configuration, F.Id("i")), Sp, Neq, Sp,
            Subscript(deleted, F.Id("i"))));

    private static Formula ReadingFormula()
    {
        Formula subsetType = Call("Finset", FinR());
        Formula summand = Seq(Call("z", F.Id("c")), Sp, Cdot, Sp,
            Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, F.Id("T")), Sp,
            Indicator(F.Id("c"), F.Id("a")));
        return Disp(Seq(
            Forall, Sp, Bound(F.Id("r"), Nat()), Comma, Sp,
            Bound(F.Id("m"), Arrow(FinR(), Nat())), Comma, RowBreak, Grp(),
            Bound(F.Id("T"), subsetType), Comma, Sp,
            Bound(F.Id("a"), Alphabet()), Comma, Sp,
            Bound(F.Id("z"), Arrow(Alphabet(), Real())), Comma, RowBreak, Grp(),
            Reading(F.Id("T"), F.Id("a"), F.Id("z")), Sp, Colon, Eq, Sp,
            Sum, Underscore, Grp(F.Id("c"), Sp, InMacro, Sp, Alphabet()), Sp,
            summand, Dot));
    }

    private static Formula ObservationNormFormula()
    {
        Formula hypothesis = Seq(Forall, Sp, F.Id("i"), Sp, InMacro, Sp, FinR(), Comma, Sp,
            D(2), Sp, Le, Sp, Subscript(F.Id("m"), F.Id("i")));
        Formula index = Seq(F.Id("T"), Sp, Subseteq, Sp, FinR(), Comma, Sp,
            F.Id("a"), Sp, InMacro, Sp, Alphabet());
        return Disp(Seq(
            Forall, Sp, Bound(F.Id("r"), Nat()), Comma, Sp,
            Bound(F.Id("m"), Arrow(FinR(), Nat())), Comma, Sp,
            hypothesis, Comma, RowBreak, Grp(),
            Bound(F.Id("z"), Arrow(Alphabet(), Real())), Comma, RowBreak, Grp(),
            Call("obsNorm", F.Id("z")), Sp, Colon, Eq, Sp,
            Operatorname, Grp(F.Id("max")), Underscore, Grp(index), Sp,
            Abs(Reading(F.Id("T"), F.Id("a"), F.Id("z"))), Dot));
    }

    private static Formula ConstantFormula()
    {
        Formula denominator = Seq(Subscript(F.Id("m"), F.Id("i")), Sp, Minus, Sp, D(1));
        Formula factor = Seq(D(2), Sp, Minus, Sp,
            Frac, Grp(D(1)), Grp(denominator));
        return Disp(Seq(
            Forall, Sp, Bound(F.Id("r"), Nat()), Comma, Sp,
            Bound(F.Id("m"), Arrow(FinR(), Nat())), Comma, RowBreak, Grp(),
            F.Id("kappa"), Open, F.Id("m"), Close, Sp, Colon, Eq, Sp,
            Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, FinR()), Sp,
            Open, factor, Close, Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula xType = Alphabet();
        Formula hypothesis = Seq(Forall, Sp, F.Id("i"), Sp, InMacro, Sp, FinR(), Comma, Sp,
            D(2), Sp, Le, Sp, Subscript(F.Id("m"), F.Id("i")));
        Formula kappa = Call("kappa", F.Id("m"));
        Formula normZ = Call("obsNorm", F.Id("z"));
        Formula pointwise = Seq(
            Forall, Sp, Bound(F.Id("c"), xType), Comma, Sp,
            Abs(Call("z", F.Id("c"))), Sp, Le, Sp,
            kappa, Sp, Cdot, Sp, normZ);
        Formula witnessEntry = Seq(
            Operatorname, Grp(F.Id("if")), Sp,
            Subscript(F.Id("c"), F.Id("i")), Sp, Eq, Sp,
            Subscript(Grp(new Formula.Power(F.Id("c"), Star)), F.Id("i")), Sp,
            Operatorname, Grp(F.Id("then")), Sp,
            D(2), Sp, Cdot, Sp, Subscript(F.Id("m"), F.Id("i")), Sp, Minus, Sp, D(3), Sp,
            Operatorname, Grp(F.Id("else")), Sp, Minus, D(1));
        Formula witness = Seq(
            Operatorname, Grp(F.Id("let")), Sp,
            F.Id("w"), Open, F.Id("c"), Close, Sp, Colon, Eq, Sp,
            Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, FinR()), Sp,
            Open, witnessEntry, Close, Comma, RowBreak, Grp());
        Formula alphabetProduct = Seq(
            Prod, Underscore, Grp(F.Id("i"), Sp, InMacro, Sp, FinR()), Sp,
            Open, Subscript(F.Id("m"), F.Id("i")), Sp, Minus, Sp, D(1), Close);
        Formula sharpness = Seq(
            Call("obsNorm", F.Id("w")), Sp, Eq, Sp, alphabetProduct, Sp,
            Land, Sp,
            Abs(Call("w", new Formula.Power(F.Id("c"), Star))), Sp, Eq, Sp,
            kappa, Sp, Cdot, Sp, Call("obsNorm", F.Id("w")));
        return Disp(Seq(
            Forall, Sp, Bound(F.Id("r"), Nat()), Comma, Sp,
            Bound(F.Id("m"), Arrow(FinR(), Nat())), Comma, Sp,
            hypothesis, Comma, RowBreak, Grp(),
            Bound(F.Id("z"), Arrow(xType, Real())), Comma, RowBreak, Grp(),
            Open, pointwise, Close, Sp, Land, Sp, RowBreak, Grp(),
            Forall, Sp, Bound(new Formula.Power(F.Id("c"), Star), xType), Comma, RowBreak, Grp(),
            witness, sharpness, Dot));
    }
}
