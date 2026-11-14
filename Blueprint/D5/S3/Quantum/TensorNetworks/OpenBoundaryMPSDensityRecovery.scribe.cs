using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.TensorNetworks;

internal sealed class OpenBoundaryMPSDensityRecoveryDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/TensorNetworks/OpenBoundaryMPSDensityRecovery";
    private static LibraryNoteRef Source => LibraryNoteRef.Create("D5/L/Geometry/critchmorton2014mps");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A raw first-three-site reduced density identifies every actual free-boundary binary bond-two competitor up to phase, conditional on a shared observable coherent chart and injective reconstructed transfer.",
        H("Open-boundary recovery from a Hermitian prefix density"),
        Blocks(
            Definition("amplitudeColumns", "Actual amplitude columns",
                "For a state ψ of length k+m, the row u and column b contain ψ at the concatenated word ub. These are coordinates of the original state, with no summation or normalization."),
            Definition("rawPrefix", "The raw Hermitian partial trace",
                "Multiply the amplitude-column matrix C by its conjugate transpose. The entry (u,v) is the sum over all complement words b of ψ(ub) times the complex conjugate of ψ(vb). This is Q_k in the displayed prefix map following Critch–Morton Conjecture 9. It preserves the norm-squared scale on the unnormalized cone; it is distinct from the coherent improperMarginal in Conjecture 8."),
            Definition("prefixMap", "The virtual prefix map",
                "The row w is l times the ordered matrix word A_w. It maps a two-dimensional right virtual vector to its prefix amplitudes, using the existing PeriodicMPSParentIntersection.wordMatrix and the bilinear complex dot product of mpsState."),
            Definition("tailMap", "Actual complement columns",
                "The column b is A_b r, with the same symbol matrices and the actual independent free right boundary r. Thus the amplitude columns factor exactly as prefixMap times tailMap."),
            Definition("transfer", "Linear transfer without a normalization assumption",
                "The map sends X to A₀ X A₀† + A₁ X A₁† on complex two by two matrices. Its m-fold iterate on rr† is the Gram matrix of the length-m complement columns. No trace-preservation, unitality or positivity of an inverse is assumed."),
            Definition("canonicalCore", "Reuse of the coherent reconstruction",
                "This is exactly OpenBoundaryMPSMarginalBirationality.reconstructedMatrix evaluated at the same three-site coherent tensor t. The supplier's chartPoly, reconstructedLeft and triple_gauge are reused with their original definitions and proof. No second support-rigidity or core-reconstruction theorem is introduced."),
            Definition("ObservableChart", "An intrinsic condition on the observed density",
                "There exists a complex vector v on three-bit words such that t = rawPrefix 3 m ψ times v has chartPoly(t) nonzero and transfer(canonicalCore t) is injective on all complex two by two matrices. Both tests depend only on the observed Q₃. The chart retains every factor of the supplier polynomial, including the reconstructed sum determinant. This definition asserts neither nonemptiness nor density."),
            Describe.Lean(DescribeId.Create("observable-chart-phase-recovery"),
                DeclarationHandle.Create(Module + ".observable_chart_phase_recovery"),
                H("Phase recovery against every actual competitor"),
                StatementSource.FromAuthor(RecoveryFormula()),
                AssessedProvenance.FromRepo(Source),
                Blocks(
                    Paragraph(Text("The target ψ and competitor φ belong to the literal parametrized image openBoundaryMPS(3+m), with arbitrary complex two by two matrices and independent free complex boundary vectors. Only ψ is required to satisfy ObservableChart. The result covers every natural m; the intended Conjecture 9 lengths have m at least one. Equality of Q₃ is equivalent to φ=zψ for a complex scalar of norm one.")),
                    Paragraph(Text("Choose t=Q₃v. For every actual realization of either state, factor its amplitude-column matrix as F₃T. Matrix multiplication gives t=F₃γ for an induced virtual vector γ. Hence the same t is an actual coherent three-site MPS for both realizations, even when the competitor parameters are singular. Apply the existing triple_gauge directly to each realization; it supplies the same reconstructed left boundary and symbol matrices. At length n the free right boundary becomes q=(s times s to the power minus n)Ur, and the physical amplitude function is unchanged.")),
                    Paragraph(Text("The chart's slice determinant factors through the rows lA_i, A₀ and the columns A_iγ. Its nonvanishing makes the rows lA_i and A₀ invertible. Restricting F₃ to the rows indexed by (i,0,0) therefore proves injectivity of F₃. This is a rank consequence of the supplied chart, not another gauge theorem.")),
                    Paragraph(Text("For the common canonical core, Q₃=F₃ E^m(qq†) F₃†. Injectivity of F₃ cancels the two sandwiches; injectivity of E cancels its iterate. Equality of the two rank-one boundary Grams gives q′=zq with norm(z)=1, including the zero-boundary case. Linearity then propagates the same phase to the whole state. Conversely a unit phase cancels against its conjugate in every raw density entry.")),
                    Paragraph(Text("This is a conditional reconstruction bridge toward Critch–Morton Conjecture 9, not an OpenProblemResolutionClaim. An intrinsic nonempty dense relative real-algebraic open locus for every length at least four, and the no-fewer clause asserting generic two-site nonidentifiability, remain obligations of the original problem. No all-interior-window interpretation is asserted.")),
                    Paragraph(Text("The gauge reconstruction is supplied by the existing Conjecture 8 formalization. The present mathematical addition is the Hermitian density bridge with a common observed coherent vector and arbitrary actual competitors. Injectivity here concerns a finite-dimensional linear map. Its algebraic inverse is not asserted to be completely positive or implementable. The theorem provides no stability, sample complexity, dynamics, time group, Hamiltonian, clock, energy or thermodynamic cost."))),
                DescribeRole.Theorem))));

    private static DocumentBlock Definition(string name, string title, string prose) =>
        Describe.Lean(DescribeId.Create("open-density-" + name.ToLowerInvariant()),
            DeclarationHandle.Create(Module + "." + name), H(title),
            StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    private static Formula RecoveryFormula()
    {
        Formula m = X("m"), p = X("ψ"), q = X("φ"), z = X("z");
        Formula n = new Formula.Binary(D(3), FormulaBinaryOperator.Add, m);
        Formula state = Arrow(At(Supplier("PeriodicMPSParentIntersection", "Word"), n), Complexes());
        Formula model = At(Supplier("OpenBoundaryMPSMarginalBirationality", "openBoundaryMPS"), n);
        Formula raw = Eq(At(Local("rawPrefix"), D(3), m, q), At(Local("rawPrefix"), D(3), m, p));
        Formula phase = Exists("z", Complexes(), And(Eq(At(Q("norm"), z), D(1)),
            Eq(q, At(Q("HSMul", "hSMul"), z, p))));
        return Disp(All("m", Seq(Mathbb, Grp(X("N"))), All("ψ", state, All("φ", state,
            Imp(Member(p, model), Imp(Member(q, model), Imp(At(Local("ObservableChart"), m, p),
                new Formula.Logic(Par(raw), FormulaLogicOperator.Iff, Par(phase)))))))));
    }

    private static Formula X(string value) => value switch
    {
        "ψ" => Psi,
        "φ" => Phi,
        _ => F.Id(value),
    };
    private static Formula Q(params string[] names)
    {
        var parts = new List<Formula>();
        foreach (var name in names) { if (parts.Count > 0) parts.Add(Dot); parts.Add(X(name)); }
        return Seq(Operatorname, Grp(Seq([.. parts])));
    }
    private static Formula Supplier(string module, string name) => Q("D5", "S3", "Quantum", "TensorNetworks", module, name);
    private static Formula Local(string name) => Supplier("OpenBoundaryMPSDensityRecovery", name);
    private static Formula At(Formula f, params Formula[] args) => new Formula.Apply(f, [.. args]);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Typed(Formula f, Formula type) => Par(Seq(f, Colon, Sp, type));
    private static Formula All(string name, Formula type, Formula body) => Seq(Forall, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula Exists(string name, Formula type, Formula body) => Seq(F.Exists, Sp, Typed(X(name), type), Comma, Sp, Par(body));
    private static Formula Imp(Formula a, Formula b) => new Formula.TypeArrow(Par(a), Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Member(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.MemberOf, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.And, Par(b));
    private static Formula Arrow(Formula a, Formula b) => new Formula.TypeArrow(a, b);
    private static Formula Complexes() => Seq(Mathbb, Grp(X("C")));
}
