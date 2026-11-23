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
            Node("euler", "Dilate the pentagonal series by substituting q to the power d for the formal indeterminate q. The formula displays the implicit ring argument R and the proof hd that d is nonzero.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                EulerFormula()),
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
                F.Disp(TupleParameters(Define(Call("markedCount", F.Id("k"), F.Id("n")), Naturals(),
                    Call("card", Call("MarkedTuple", F.Id("k"), F.Id("n"))))))),
            Node("markedPartitionFintype", "The type of markings of partitions of a fixed size is finite. SigmaFintype and PiFintype denote the inferred dependent sum and dependent function instances for the indicated finite families. An index typed by a finite set ranges over its member subtype, and .1 extracts its underlying value.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                MarkedPartitionFintypeFormula()),
            Node("markedTupleFintype", "There are finitely many ordered marked tuples at fixed component count and total size.", DescribeRole.Definition, AssessedProvenance.FromRepo(Source),
                MarkedTupleFintypeFormula()),
            Node("F", "The Euler quotient over R. The factor f indexed by d and R is euler at degree d over R with its nonzero degree proof. invOfUnit inverts the denominator with constant coefficient one.", DescribeRole.Definition, AssessedProvenance.FromLiterature(Source),
                F.Disp(RingParameters(Define(Call("F", F.Id("R")), Series(),
                    F.Seq(Euler(6), F.Thin, Call("invOfUnit", F.Seq(Euler(1), F.Thin, Euler(2), F.Thin, Euler(3)), F.D(1))))))),
            Node("F_const", "The Euler quotient has constant coefficient one.", DescribeRole.Theorem, AssessedProvenance.FromRepo(Source)),
            Node("marked_count_coeff", "For all natural k and n, the integer cast of the tuple count equals the coefficient of degree n in F raised to k.", DescribeRole.Theorem, AssessedProvenance.FromLiterature(Source))),
        []));

    private static DocumentBlock Node(
        string declaration, string narrative, DescribeRole role, AssessedProvenance provenance, Formula? formula = null) =>
        Describe.Lean(DescribeId.Create("designatedsummands-" + declaration.ToLowerInvariant().Replace('_', '-').Replace('₀', '0')),
            DeclarationHandle.Create(Prefix + declaration), H(declaration),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(formula),
            provenance, Blocks(Paragraph(Text(narrative))), role);

    private static Formula EulerFormula()
    {
        var ring = F.Id("R");
        var degree = F.Id("d");
        var guard = F.Id("hd");
        return F.Disp(EulerParameters(Define(Call("euler", ring, degree, guard), Series(),
            Call("expand", degree, guard, Call("pentagonalSeries", ring)))));
    }

    private static Formula EtaUnitFormula()
    {
        var euler = Call("euler", F.Id("R"), F.Id("d"), F.Id("hd"));
        return F.Disp(EulerParameters(Define(Call("etaUnit", F.Id("R"), F.Id("d"), F.Id("hd")),
            Call("Units", Series()), F.Seq(F.Langle, euler, F.Comma, F.Sp,
                Call("invOfUnit", euler, F.D(1)), F.Rangle))));
    }

    private static Formula MarkedPartitionFormula() => F.Disp(PartitionParameters(
        Define(Call("MarkedPartition", F.Id("n")), F.Id("Type"),
        Dependent(F.Sigma, F.Id("p"), Call("Partition", F.Id("n")),
            Dependent(F.Pi, F.Id("i"), PartSizes(), Occurrences())))));

    private static Formula MarkedTupleFormula() => F.Disp(TupleParameters(
        Define(Call("MarkedTuple", F.Id("k"), F.Id("n")), F.Id("Type"),
        Dependent(F.Sigma, F.Id("l"), DegreeAssignments(),
            Dependent(F.Pi, F.Id("i"), Positions(), Component())))));

    private static Formula MarkedPartitionFintypeFormula() =>
        F.Disp(PartitionParameters(Define(Call("markedPartitionFintype", F.Id("n")),
            Call("Fintype", Call("MarkedPartition", F.Id("n"))),
            Call("SigmaFintype", Call("Partition", F.Id("n")), Family(F.Id("p"), Call("Partition", F.Id("n")),
                Call("PiFintype", PartSizes(), Family(F.Id("i"), PartSizes(), Occurrences())))))));

    private static Formula MarkedTupleFintypeFormula() =>
        F.Disp(TupleParameters(Define(Call("markedTupleFintype", F.Id("k"), F.Id("n")),
            Call("Fintype", Call("MarkedTuple", F.Id("k"), F.Id("n"))),
            Call("SigmaFintype", DegreeAssignments(), Family(F.Id("l"), DegreeAssignments(),
                Call("PiFintype", Positions(), Family(F.Id("i"), Positions(),
                    Call("markedPartitionFintype", Degree()))))))));

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

    private static Formula Family(Formula index, Formula domain, Formula body) =>
        F.Seq(F.LambdaLower, F.Sp, Typed(index, domain), F.Comma, F.Sp, body);

    private static Formula Euler(byte degree) =>
        new Formula.Subscript(F.Id("f"), F.Seq(F.D(degree), F.Comma, F.Sp, F.Id("R")));
    private static Formula Naturals() => F.Seq(F.Mathbb, F.Grp(F.Id("N")));
    private static Formula Series() => Call("PowerSeries", F.Id("R"));
    private static Formula Typed(Formula name, Formula type) =>
        F.Seq(F.Open, name, F.Colon, F.Sp, type, F.Close);
    private static Formula RingParameters(Formula body) =>
        F.Seq(F.Forall, F.Sp, Typed(F.Id("R"), F.Id("Type")), F.Sp,
            F.OpenBracket, Call("CommRing", F.Id("R")), F.CloseBracket, F.Comma, F.Sp, body);
    private static Formula EulerParameters(Formula body) =>
        RingParameters(F.Seq(F.Forall, F.Sp, Typed(F.Id("d"), Naturals()), F.Sp,
            Typed(F.Id("hd"), F.Seq(F.Id("d"), F.Sp, F.Neq, F.Sp, F.D(0))), F.Comma, F.Sp, body));
    private static Formula PartitionParameters(Formula body) =>
        F.Seq(F.Forall, F.Sp, Typed(F.Id("n"), Naturals()), F.Comma, F.Sp, body);
    private static Formula TupleParameters(Formula body) =>
        F.Seq(F.Forall, F.Sp, Typed(F.Seq(F.Id("k"), F.Sp, F.Id("n")), Naturals()), F.Comma, F.Sp, body);
    private static Formula Define(Formula left, Formula type, Formula right) =>
        F.Seq(left, F.Sp, F.Colon, F.Sp, type, F.Sp, F.Colon, F.Eq, F.Sp, right);
}
