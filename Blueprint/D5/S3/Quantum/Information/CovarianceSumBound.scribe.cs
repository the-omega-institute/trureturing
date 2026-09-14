using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Information;

internal sealed class CovarianceSumBoundDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Information/CovarianceSumBound.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For a finite-dimensional density state, symmetrized covariance satisfies "
            + "Cauchy-Schwarz. A spectral interval of half width Delta and sparse row "
            + "supports bound the total absolute covariance.",
        H("Density-state covariance and its sparse sum"),
        Blocks(
            Result("expectation", "expectation", "Real expectation",
                "The state is a positive semidefinite complex matrix of trace one. "
                    + "All carriers are arbitrary finite types; singular states are included.",
                Eqn(E(F.Id("A")), Seq(Re, Sp, Call("tr", Seq(Rho, Sp, F.Id("A"))))),
                DescribeRole.Definition, literature: "D5/L/Quantum/gibilisco2007covariance"),
            Result("covariance", "covariance", "Symmetrized covariance",
                "For Hermitian A and B this is one half the expectation of AB+BA "
                    + "minus the product of expectations. A and B need not commute.",
                Eqn(C(F.Id("A"), F.Id("B")), Seq(Frac,
                    Grp(E(Seq(F.Id("A"), F.Id("B"))), Sp, Plus, Sp,
                        E(Seq(F.Id("B"), F.Id("A")))), Grp(Num(2)), Sp, Minus, Sp,
                    E(F.Id("A")), Sp, E(F.Id("B")))), DescribeRole.Definition,
                literature: "D5/L/Quantum/gibilisco2007covariance"),
            Result("variance", "variance", "Variance",
                "Variance uses the same state and the same expectation as covariance.",
                Eqn(V(F.Id("A")), Seq(E(Sq(F.Id("A"))), Sp, Minus, Sp,
                    Sq(E(F.Id("A"))))), DescribeRole.Definition,
                literature: "D5/L/Quantum/gibilisco2007covariance"),
            Result("symmetry", "covariance_symm", "Symmetry",
                "Exchanging the two observables preserves symmetrized covariance.",
                Eqn(C(F.Id("A"), F.Id("B")), C(F.Id("B"), F.Id("A"))),
                literature: "D5/L/Quantum/gibilisco2007covariance"),
            Result("additivity", "covariance_add_right", "Right additivity",
                "For every fixed state and A, covariance is additive in its right argument.",
                Eqn(C(F.Id("A"), Seq(F.Id("B"), Plus, F.Id("C"))),
                    Seq(C(F.Id("A"), F.Id("B")), Sp, Plus, Sp,
                        C(F.Id("A"), F.Id("C")))),
                literature: "D5/L/Quantum/petz2001covariance"),
            Result("self", "covariance_self", "Self-covariance is variance",
                "The two definitions agree on equal observables.",
                Eqn(C(F.Id("A"), F.Id("A")), V(F.Id("A"))),
                literature: "D5/L/Quantum/gibilisco2007covariance"),
            Result("nonnegative", "variance_nonneg", "Variance is nonnegative",
                "For a Hermitian observable, its centered square has nonnegative expectation.",
                Disp(Seq(Num(0), Sp, Le, Sp, V(F.Id("A")))),
                literature: "D5/L/Quantum/petz2001covariance"),
            Result("cauchy-schwarz", "abs_covariance_le", "Cauchy-Schwarz in a density state",
                "For Hermitian A and B, centered observables belong to the weighted matrix "
                    + "semi-inner product space. Its real pairing is exactly covariance.",
                Disp(Seq(Abs(C(F.Id("A"), F.Id("B"))), Sp, Le, Sp,
                    Sqrt, Grp(V(F.Id("A")), Sp, V(F.Id("B"))))),
                literature: "D5/L/Quantum/mathlib2026covariance"),
            Result("half-width", "variance_le_half_width_sq", "Spectral half-width bound",
                "Assume Delta is nonnegative and every spectral value of Hermitian A lies "
                    + "in [c-Delta,c+Delta]. Delta is the half width. Continuous functional "
                    + "calculus bounds the square centered at c, and subtracting the squared "
                    + "mean displacement bounds the variance.",
                Disp(Seq(V(F.Id("A")), Sp, Le, Sp, Sq(Delta))),
                literature: "D5/L/Quantum/mathlib2026covariance"),
            Result("variance-sum", "covariance_sum_le_of_variance", "Sum from variance bounds",
                "On a finite set Q, assume every R(x) is Hermitian, each variance is at most "
                    + "Delta squared, and for each x in Q at most b elements y in Q have "
                    + "nonzero covariance. Summing only these supports gives the bound.", SumBound(),
                literature: "D5/L/Quantum/axler2024innerproduct"),
            Result("spectral-sum", "covariance_sum_le", "Sparse covariance sum bound",
                "For a finite set Q and a density state, assume all R(x), x in Q, are Hermitian "
                    + "with spectra in [c(x)-Delta,c(x)+Delta], where Delta is nonnegative. "
                    + "For every x in Q the support of y mapped to Cov(R(x),R(y)) has at most "
                    + "b elements in Q. Then the bound follows with N equal to card Q. "
                    + "The support hypothesis is the locality input; the theorem does not "
                    + "derive a propagation or preparation-time bound.", SumBound(),
                literature: "D5/L/Quantum/sharma2010variance"))));

    private static DocumentBlock Result(string id, string declaration, string title, string prose,
        Formula formula, DescribeRole role = DescribeRole.Theorem,
        string literature = "D5/L/Quantum/mathlib2026covariance") =>
        Describe.Lean(DescribeId.Create("covsum-" + id), DeclarationHandle.Create(Module + declaration),
            H(title), StatementSource.FromAuthor(formula),
            AssessedProvenance.FromLiterature(LibraryNoteRef.Create(literature)),
            Blocks(Paragraph(Text(prose))), role);

    private static Formula E(Formula a) => Call("E", Rho, a);
    private static Formula V(Formula a) => Call("Var", Rho, a);
    private static Formula C(Formula a, Formula b) => Call("Cov", Rho, a, b);
    private static Formula Sq(Formula a) => Seq(Grp(a), Caret, Grp(Num(2)));
    private static Formula Abs(Formula a) => Seq(Lvert, Sp, a, Sp, Rvert);
    private static Formula Eqn(Formula a, Formula b) => Disp(Seq(a, Sp, Eq, Sp, b));
    private static Formula SumBound() => Disp(Seq(
        Sum, Underscore, Grp(F.Id("x"), Comma, F.Id("y"), Sp, InMacro, Sp, F.Id("Q")), Sp,
        Abs(C(Call("R", F.Id("x")), Call("R", F.Id("y")))), Sp, Le, Sp,
        Call("card", F.Id("Q")), Sp, F.Id("b"), Sp, Sq(Delta)));
}
