using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Partitions;

internal sealed class DesignatedSummandsDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Partitions/DesignatedSummands.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/Fourier/yaqubi2026designatedsummands");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The coefficient of the Euler quotient counts ordered tuples with an actual designated occurrence.",
        H("Ordered tuples with designated summands"),
        Blocks(
            Paragraph(Text("For each distinct part size of multiplicity m, a marked partition carries a choice in Fin m. An ordered tuple uses a degree assignment on the component positions with total degree n. A component of degree zero is the empty partition. The local multiplicity series is 1 plus the sum of m times q to the power im for positive m, where i is the part size. Multiplying its Euler denominators gives the factor in degree 6i. Taking the product over all part sizes yields the quotient F, and coefficient convolution gives the ordered tuple count.")),
            Node("euler", "Dilate the pentagonal series over a commutative ring R by a positive natural degree d. P denotes PowerSeries.pentagonalSeries.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                Define(Call("euler", F.Id("d")), new Formula.Apply(new Formula.Subscript(F.Id("P"), F.Id("R")), [new Formula.Power(F.Id("q"), F.Id("d"))]))),
            Node("etaUnit", "The corresponding unit, with inverse at constant coefficient one.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                EtaUnitFormula()),
            Node("tendsto_expand_discrete", "Dilation is continuous for coefficientwise convergence over a discrete ring.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_tendsto", "The finite Euler products with exponents d(i+1) converge to the dilated series.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("euler_const", "The constant coefficient of a dilated Euler product is one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("map_eta", "A ring homomorphism on the coefficients preserves the dilated Euler unit.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("expand_eta", "Dilating an Euler unit again multiplies its dilation index.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("MarkedPartition", "A partition of n together with one choice of actual occurrence for each part size present. parts is the multiset of parts, toFinset forgets repeated sizes, and Fin m has indices from zero through m − 1.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                MarkedPartitionFormula()),
            Node("MarkedTuple", "An ordered tuple of k marked partitions with total size n. Each position may have degree zero. The finsuppAntidiag indexes finitely supported degree assignments on the natural numbers with support contained in range k and total degree n.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                MarkedTupleFormula()),
            Node("markedCount", "The cardinality of the type of ordered marked tuples.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Define(Call("markedCount", F.Id("k"), F.Id("n")), Call("card", Call("MarkedTuple", F.Id("k"), F.Id("n"))))),
            Node("markedPartitionFintype", "The type of markings of partitions of a fixed size is finite. SigmaFintype and PiFintype denote the inferred dependent sum and dependent function instances for the indicated finite families.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                MarkedPartitionFintypeFormula()),
            Node("markedTupleFintype", "There are finitely many ordered marked tuples at fixed component count and total size.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                MarkedTupleFintypeFormula()),
            Node("F", "The Euler quotient f6 divided by f1 f2 f3 as a formal power series. Each f with index d is euler d, and the denominator is inverted as a unit of constant coefficient one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                Define(F.Id("F"), F.Seq(Euler(6), F.Thin, new Formula.Power(Parens(F.Seq(Euler(1), F.Thin, Euler(2), F.Thin, Euler(3))), F.Seq(F.Minus, F.D(1)))))),
            Node("F_const", "The Euler quotient has constant coefficient one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("marked_count_coeff", "For all natural k and n, the integer cast of the tuple count equals the coefficient of degree n in F raised to k.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("designatedsummands-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(narrative))), role);

    private static Formula EtaUnitFormula()
    {
        var euler = Call("euler", F.Id("d"));
        return Define(Call("etaUnit", F.Id("d")),
            F.Seq(F.Langle, euler, F.Comma, F.Sp, Call("invOfUnit", euler, F.D(1)), F.Rangle));
    }

    private static Formula MarkedPartitionFormula() => Define(Call("MarkedPartition", F.Id("n")),
        Dependent(F.Sigma, F.Id("p"), Call("Partition", F.Id("n")),
            Dependent(F.Prod, F.Id("i"), PartSizes(), Occurrences())));

    private static Formula MarkedTupleFormula() => Define(Call("MarkedTuple", F.Id("k"), F.Id("n")),
        Dependent(F.Sigma, F.Id("l"), DegreeAssignments(),
            Dependent(F.Prod, F.Id("i"), Positions(), Component())));

    private static Formula MarkedPartitionFintypeFormula() =>
        Define(Call("markedPartitionFintype", F.Id("n")),
            Call("SigmaFintype", Call("Partition", F.Id("n")), Family(F.Id("p"),
                Call("PiFintype", PartSizes(), Family(F.Id("i"), Occurrences())))));

    private static Formula MarkedTupleFintypeFormula() =>
        Define(Call("markedTupleFintype", F.Id("k"), F.Id("n")),
            Call("SigmaFintype", DegreeAssignments(), Family(F.Id("l"),
                Call("PiFintype", Positions(), Family(F.Id("i"),
                    Call("markedPartitionFintype", Degree()))))));

    private static Formula Parts() => Call("parts", F.Id("p"));
    private static Formula PartSizes() => Call("toFinset", Parts());
    private static Formula Occurrences() => Call("Fin", Call("count", Parts(), Underlying(F.Id("i"))));
    private static Formula Positions() => Call("range", F.Id("k"));
    private static Formula DegreeAssignments() => Call("finsuppAntidiag", Positions(), F.Id("n"));
    private static Formula Degree() => new Formula.Apply(Underlying(F.Id("l")), [Underlying(F.Id("i"))]);
    private static Formula Component() => Call("MarkedPartition", Degree());
    private static Formula Underlying(Formula value) => F.Seq(value, F.Dot, F.D(1));

    private static Formula Dependent(Formula @operator, Formula index, Formula domain, Formula body) =>
        F.Seq(new Formula.Subscript(@operator, F.Seq(index, F.Colon, F.Sp, domain)), F.Sp, body);

    private static Formula Family(Formula index, Formula body) =>
        F.Seq(F.LambdaLower, F.Sp, index, F.Comma, F.Sp, body);

    private static Formula Euler(byte degree) => new Formula.Subscript(F.Id("f"), F.D(degree));
    private static Formula Parens(Formula value) => F.Seq(F.Open, value, F.Close);
    private static Formula Define(Formula left, Formula right) =>
        F.Disp(F.Seq(left, F.Sp, F.Colon, F.Eq, F.Sp, right));
}
