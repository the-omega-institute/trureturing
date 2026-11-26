using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Gauge;

internal sealed class KobayashiMaskawaJarlskogRigidityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Quantum/Gauge/KobayashiMaskawaJarlskogRigidity.";
    private static readonly LibraryNoteRef KobayashiMaskawa =
        LibraryNoteRef.Create("D5/L/LieTheory/kobayashimaskawa1973cpviolation");
    private static readonly LibraryNoteRef Jarlskog =
        LibraryNoteRef.Create("D5/L/LieTheory/jarlskog1985commutator");

    private static readonly LibraryNoteRef Unistochastic =
        LibraryNoteRef.Create("D5/L/LieTheory/dunklzyczkowski2009unistochastic");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Quark mixing phases and gauge beta coefficients constrain the generation count.",
        H("Quark mixing and the generation count"),
        Blocks(
            Paragraph(Text("Indices start at zero. For a complex matrix V, the quartet Q(i,j,k,l) "
                + "is Vᵢⱼ Vₖₗ times the conjugate of Vᵢₗ Vₖⱼ. The invariant J(V) is the imaginary "
                + "part of Q(0,1,1,2). The symbol e is alternating with e₀₁₂ = 1.")),
            Node("quartet-rephasing", "quartet_biRephase_invariant", "Two-sided quartet invariance",
                "For every natural dimension and every complex square matrix, multiplying entry "
                + "(i,j) by αᵢ and the conjugate of βⱼ preserves every quartet when each phase has "
                + "norm one. Each row or column phase appears once with its conjugate."),
            Node("two-generations-rephasing", "u2_real_rephasable", "Real representatives in dimension two",
                "Every two-dimensional unitary matrix admits norm-one row and column phases "
                + "making the imaginary part of every entry zero. Orthogonality makes the sum "
                + "of the two column quartet imaginary parts vanish, and the repeated-column "
                + "term is already real. The phase construction also permits zero entries.",
                source: KobayashiMaskawa),
            Node("two-generation-quartets", "u2_all_quartets_real", "Quartets in dimension two",
                "For every two-dimensional unitary matrix, all quartets have zero imaginary part. "
                + "The sum of the imaginary parts over the two column choices vanishes, and the quartet with repeated columns is real."),
            Node("three-generation-lower-bound", "cp_violation_requires_three_generations",
                "A nonreal quartet requires three generations",
                "If a finite-dimensional unitary matrix has a quartet with nonzero imaginary "
                + "part, its dimension is at least three. Dimension zero has no index, dimension "
                + "one has repeated indices, and dimension two has a real representative.",
                source: KobayashiMaskawa),
            Node("universal-jarlskog", "jarlskog_universal_all_quartets",
                "One invariant gives every imaginary quartet",
                "For every three-dimensional unitary V and all four indices, orthogonality "
                + "gives zero sums over either of the two varying indices. Alternation then "
                + "leaves one real value for the chosen orientation.",
                Seq(ImOf(Seq(F.Id("Q"), Open, F.Id("i"), Comma, F.Id("j"), Comma, F.Id("k"), Comma, F.Id("l"), Close)),
                    Eq, J(F.Id("V")), Sum, Underscore, Grp(F.Id("m")), Sum, Underscore, Grp(F.Id("n")),
                    Epsilon("ikm"), Epsilon("jln")),
                Jarlskog),
            Node("jarlskog-sharp-bound", "jarlskog_abs_le_sharp", "Sharp absolute bound",
                "For every three-dimensional unitary V, the products V₀ⱼ times the conjugates of V₁ⱼ form a closed triangle "
                + "with perimeter at most one. Twice the area is the absolute imaginary quartet. "
                + "Heron's identity and the arithmetic–geometric mean inequality bound the area.",
                Seq(Bar, J(F.Id("V")), Bar, Leq, SharpConstant()), Unistochastic),
            Node("fourier-attainment", "fourier3_attains_max_jarlskog", "Fourier attainment",
                "The entries of F₃ are ω to the power jk divided by √3, where "
                + "ω = −1/2 + i√3/2. This matrix is unitary and its chosen quartet has "
                + "positive imaginary part.",
                Seq(Fourier(), Sp, InMacro, Sp, F.Id("U"), Open, D(3), Close, Sp, Land, Sp,
                    Bar, J(Fourier()), Bar, Eq, SharpConstant()), Unistochastic),
            Node("three-generations-reality", "u3_jarlskog_zero_iff_real_rephasable",
                "Vanishing and real representatives",
                "A three-dimensional unitary matrix satisfies J(V) = 0 exactly when "
                + "norm-one row and column phases make every entry real. If some row has "
                + "three nonzero entries, it fixes the column phases. Otherwise, two rows "
                + "with two nonzero entries must have the same support, since orthogonal "
                + "rows cannot have exactly one common nonzero entry.", source: Unistochastic),
            Node("commutator-determinant", "jarlskog_commutator_det", "Mass commutator determinant",
                "Let Hᵤ = Uᵤ diag(dᵤ) Uᵤ† and H_d = U_d diag(d_d) U_d†, where both U are "
                + "three-dimensional unitary matrices and both diagonals are real. Set "
                + "V = Uᵤ† U_d. For either diagonal d, Δ(d) = (d₁ − d₀)(d₂ − d₀)(d₂ − d₁). "
                + "The determinant is nonzero exactly when J(V) is nonzero and both "
                + "spectra have distinct entries.",
                Seq(F.Id("det"), Open, Minus, F.Id("i"), OpenBracket, Sub("H", "u"), Comma, Sub("H", "d"),
                    CloseBracket, Close, Eq, Minus, D(2), J(F.Id("V")),
                    DeltaOf(Sub("d", "u")), DeltaOf(Sub("d", "d"))),
                Jarlskog),
            Node("sm-ratio", "sm_unification_ratio_generation_independent",
                "One-loop Standard Model ratio",
                "Let N_g and N_H be rational and N_H differ from 110. The coefficient "
                + "triple is (4N_g/3 + N_H/10, −22/3 + 4N_g/3 + N_H/6, −11 + 4N_g/3). "
                + "The common generation term cancels from both differences.",
                Seq(Frac, Grp(Sub("b", D(2)), Minus, Sub("b", D(3))),
                    Grp(Sub("b", D(1)), Minus, Sub("b", D(2))), Eq,
                    Frac, Grp(D(1, 1, 0), Plus, D(5), Sub("N", "H")),
                    Grp(D(2, 2, 0), Minus, D(2), Sub("N", "H")))),
            Node("sm-mssm-ratios", "sm_mssm_unification_ratios", "Standard Model and MSSM values",
                "For every rational N_g, the one-doublet Standard Model ratio is 115/218. "
                + "The MSSM triple (2N_g + 3/5, −5 + 2N_g, −9 + 2N_g) gives 5/7. "
                + "These rational values are distinct."),
            Node("generation-window", "qcd_confinement_and_cp_generation_window",
                "Three-color two-loop coefficient window",
                "For natural N_g and N_c = 3, the coefficients are b₀ = 11 − 4N_g/3 and "
                + "b₁ = 102 − 76N_g/3. The inequality b₀ > 0 is equivalent to N_g ≤ 8, "
                + "and b₁ > 0 is equivalent to N_g ≤ 4. Both strict inequalities together "
                + "with N_g ≥ 3 hold exactly at N_g = 3 or N_g = 4. In the two-loop "
                + "beta polynomial, positivity of both coefficients excludes a positive "
                + "perturbative fixed point. The window constrains the coefficient signs."))));

    private static DocumentBlock Node(string id, string name, string title, string prose,
        Formula? formula = null, LibraryNoteRef? source = null) =>
        Describe.Lean(DescribeId.Create(id), DeclarationHandle.Create(Prefix + name), H(title),
            formula is null ? StatementSource.WithoutFormula() : StatementSource.FromAuthor(Disp(formula)),
            source is null ? AssessedProvenance.FromRepo() : AssessedProvenance.FromLiterature(source),
            Blocks(Paragraph(Text(prose))), DescribeRole.Theorem);

    private static Formula Sub(string symbol, string index) => Sub(symbol, F.Id(index));
    private static Formula Sub(string symbol, Formula index) => Seq(F.Id(symbol), Underscore, Grp(index));
    private static Formula Fourier() => Sub("F", D(3));
    private static Formula J(Formula matrix) => Seq(F.Id("J"), Open, matrix, Close);
    private static Formula ImOf(Formula value) => Seq(Operatorname, Grp(F.Id("Im")), Open, value, Close);
    private static Formula Epsilon(string indices) => Sub("e", indices);
    private static Formula DeltaOf(Formula values) => Seq(Delta, Open, values, Close);
    private static Formula SharpConstant() => Seq(Frac, Grp(D(1)), Grp(D(6), Sqrt, Grp(D(3))));
}
