using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumChannels.ProjectionDiagnostics;

internal sealed class MonitoredSpectralMeanDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The monitored mean counts distinct occupied eigenvalues.",
        H("Finite dimensional monitored spectral mean"),
        Blocks(Describe.Lean(
            DescribeId.Create("monitored-spectral-mean"),
            DeclarationHandle.Create("D5/S3/QuantumChannels/ProjectionDiagnostics/MonitoredSpectralMean.monitored_spectral_mean"),
            H("The weighted first return law"),
            StatementSource.FromAuthor(Statement()),
            AssessedProvenance.FromLiterature(
                LibraryNoteRef.Create("D5/L/HilbertOperators/grunbaum2013recurrence")),
            Blocks(Paragraph(Text(
                "Let U be unitary on a finite dimensional complex inner product space E, and let v have norm one. "
                + "At each step the protocol applies U and tests the orthogonal projection onto the line spanned by v. "
                + "A failed test leaves the unnormalized state T x, where T=(I-P)U. "
                + "Thus p(n+1) is the squared modulus of the inner product of v with U T^n v. "
                + "The set S consists of the complex numbers lambda for which some ambient vector w satisfies "
                + "U w=lambda w and the inner product of w with v is nonzero. "
                + "The cardinality counts different complex numbers, irrespective of eigenspace multiplicity. "
                + "C is the span of the actual forward orbit U^n v.")),
                Paragraph(Text(
                "The restriction of U to C is surjective because it is an injective endomorphism of a finite dimensional space. "
                + "On C the right defect of A=T restricted to C is the rank one operator determined by v. "
                + "Its finite telescope gives the survival sum as dim C minus the trace of A^H(A^H)*. "
                + "Finite summation by parts subtracts the further term H times the survival probability at H. "
                + "A strictly contracting positive power bounds both remainders on cofinal horizons H=kN; "
                + "the bound for the second remainder uses k times a geometric sequence. "
                + "Nonnegative partial sums then give the stated HasSum, including convergence.")),
                Paragraph(Text(
                "An orthonormal eigenbasis of the same cyclic unitary has nonzero initial overlaps. "
                + "Two equal eigenvalues would give a nonzero eigenvector with zero initial overlap, contradicting the zero future kernel. "
                + "Conversely an ambient occupied eigenvector projects to a nonzero cyclic eigenvector, because orthogonal projection "
                + "onto C preserves its overlap with v and commutes with U. Expansion in the cyclic eigenbasis identifies its eigenvalue. "
                + "This proves both inclusions between S and the range of the cyclic eigenvalue map. "
                + "The result concerns this pure state return test. It does not assert a mean formula for arbitrary instruments."))),
            DescribeRole.Theorem))));

    private static Formula Paren(params Formula[] content) => Seq(Open, Seq(content), Close);
    private static Formula Bind(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);

    private static Formula Statement()
    {
        Formula e = F.Id("E"), u = F.Id("U"), v = F.Id("v"), n = F.Id("n");
        Formula complex = Seq(Mathbb, Grp(F.Id("C")));
        Formula real = Seq(Mathbb, Grp(F.Id("R")));
        Formula natural = Seq(Mathbb, Grp(F.Id("N")));
        Formula support = Call("occupiedSpectrum", u, v);
        Formula card = Call("ncard", support);
        Formula term = Seq(Paren(n, Plus, D(1)), Cdot, Sp,
            Call("returnProbability", u, v, Seq(n, Plus, D(1))));
        Formula sum = Call("HasSum", Seq(Paren(n, Colon, natural), Mapsto, Sp, term), Call("cast", card, real));
        Formula result = And(Call("Finite", support), And(
            Seq(card, Eq, Call("finrank", complex, Call("cyclicSpace", u, v))), sum));
        Formula law = new Formula.Logic(Seq(new Formula.Norm(v), Eq, D(1)),
            FormulaLogicOperator.Implies, result);
        return Disp(Bind("E", F.Id("Type"), Seq(
            OpenBracket, Call("NormedAddCommGroup", e), CloseBracket, Sp,
            OpenBracket, Call("InnerProductSpace", complex, e), CloseBracket, Sp,
            OpenBracket, Call("FiniteDimensional", complex, e), CloseBracket, Comma, Quad,
            Bind("U", Call("LinearIsometryEquiv", complex, e, e), Bind("v", e,
                law)))));
    }
}
