using static StrataLint.Scribe.DefinitionDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.SpectralGraph;

internal sealed class BoundaryHeatFullVisibilityObstructionDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/SpectralGraph/BoundaryHeatFullVisibilityObstruction.";

    private static readonly LibraryNoteRef KronBackground =
        LibraryNoteRef.Create("D5/L/GraphInvariants/dorflerbullo2013kron");

    public DocumentDefinition Create()
    {
        Formula l = F.Id("L");
        Formula reflected = F.Id("M");
        Formula t = F.Id("t");
        Formula h = F.Id("h");
        Formula real = F.Seq(F.Mathbb, F.Grp(F.Id("R")));
        Formula heat = Call("heat", l, t);
        Formula curve = Add(Add(Add(Ratio(1, 4), Decay(4, 12, t)), Decay(5, 6, t)), Decay(6, 2, t));
        Formula heatEquality = All("t", real, Eqn(heat, Call("heat", reflected, t)));
        Formula commonCurve = All("t", real, Eqn(heat, curve));
        Formula determinants = And(Ne(Call("det", Call("frame", l, h)), F.D(0)),
            Ne(Call("det", Call("frame", reflected, h)), F.D(0)));
        Formula visibility = All("h", real, new Formula.Logic(
            new Formula.Relation(F.D(0), FormulaRelationOperator.LessThan, h),
            FormulaLogicOperator.Implies, determinants));
        Formula firstMaximum = Call("IsGreatest", Call("conductanceValues", l), Ratio(11, 6));
        Formula reflectedMaximum = Call("IsGreatest", Call("conductanceValues", reflected), Ratio(16, 9));
        Formula differentConductances = Ne(Call("edgeConductances", l), Call("edgeConductances", reflected));
        Formula nonisomorphic = new Formula.Not(Call("IsWeightedIso", l, reflected));
        Formula statement = And(Call("IsK4Laplacian", l),
            And(Call("IsK4Laplacian", reflected),
                And(heatEquality,
                    And(commonCurve,
                        And(visibility,
                            And(firstMaximum,
                                And(reflectedMaximum,
                                    And(differentConductances, nonisomorphic))))))));

        return DocumentDefinition.Create(ScribeNode.Create(
            "Equal one-port heat for all real times can coexist with full sampled visibility and distinct weighted graph laws.",
            H("One-port heat does not identify the weighted complete graph"),
            Blocks(
                Paragraph(Text("Both networks have vertex set Fin 4, unit masses, six positive conductances, and excitation and measurement at coordinate 0. In the displayed statement M denotes the Lean matrix reflectedL.")),
                Definition("matrix", "Matrix space", "Mat", "Real matrices with rows and columns indexed by Fin 4."),
                Definition("laplacian", "First Laplacian", "L",
                    "The rows of 6L are (25, −11, −8, −6), (−11, 25, −8, −6), (−8, −8, 22, −6), and (−6, −6, −6, 18)."),
                Definition("reflection", "Port-fixing reflection", "U",
                    "For the column v = (0, 1, 1, −2), the matrix U is the identity minus vvᵀ/3. It fixes coordinate vector e₀ and the all-ones vector."),
                Definition("reflected-laplacian", "Reflected Laplacian", "reflectedL",
                    "The second Laplacian M is ULUᵀ. The rows of 54M are (225, −78, −51, −96), (−78, 202, −86, −38), (−51, −86, 193, −56), and (−96, −38, −56, 190)."),
                Definition("weighted-complete", "Weighted complete Laplacian", "IsK4Laplacian",
                    "IsK4Laplacian requires symmetry, zero row sums, and strictly negative off-diagonal entries."),
                Definition("step", "Heat evolution", "heatStep",
                    "At a real t the heat matrix for A is the matrix exponential of −tA."),
                Definition("readout", "Scalar heat at the port", "boundaryHeat",
                    "The function heat(A, t) is the (0, 0) entry of the heat matrix."),
                Definition("frame", "Sampled Krylov frame", "krylovFrame",
                    "Column j of frame(A, h), for j from 0 through 3, is the jth power of the heat matrix at h applied to e₀."),
                Definition("conductances", "Edge conductance multiset", "edgeConductances",
                    "Take the negatives of the six strictly upper-triangular entries, counting multiplicities."),
                Definition("values", "Conductance value set", "conductanceValues",
                    "Take all values −Aᵢⱼ for distinct indices i and j."),
                Definition("weighted-isomorphism", "Weighted graph isomorphism", "IsWeightedIso",
                    "IsWeightedIso(A, B) means that some permutation of all four vertices preserves each off-diagonal conductance. The permutation is arbitrary, including its action on vertex 0."),
                Describe.Lean(DescribeId.Create("boundary-heat-obstruction"),
                    DeclarationHandle.Create(Prefix + "boundary_heat_full_visibility_obstruction"),
                    H("Equal heat and full visibility with unequal graph weights"),
                    StatementSource.FromAuthor(F.Disp(statement)), AssessedProvenance.FromRepo(KronBackground),
                    Blocks(
                        Paragraph(Text("The proof diagonalizes L with eigenvalues 0, 4, 5 and 6. Their port spectral masses are 1/4, 1/12, 1/6 and 1/2. The matrix exponential respects U-conjugation and U fixes the port, so the scalar curves agree for every real t. For every h > 0 the four heat eigenvalues are distinct. The four columns factor through the eigenbasis, a diagonal of nonzero port coefficients and the Vandermonde matrix on the heat eigenvalues. Conjugation transports the invertible frame to M.")),
                        Paragraph(Text("Direct entry checks give strictly positive conductances and zero row sums for each symmetric matrix. The largest conductances are 11/6 for L and 16/9 for M. A weighted isomorphism would preserve that maximum under any vertex permutation, which proves the obstruction even when the port label may move.")),
                        Paragraph(Text("The 1966 paper by Ho and Kalman, Effective construction of linear state-variable models from input/output functions, supplies the classical realization context for sampled input-output data. Here the two fully visible realizations are orthogonally equivalent by U. The paper by Dörfler and Bullo supplies electrical-network background on Schur-complement elimination. The displayed result concerns the heat curve, the sampled Krylov frames and the graph weights."))),
                    DescribeRole.Theorem))));
    }

    private static DocumentBlock Definition(string id, string title, string name, string description) =>
        Describe.Lean(DescribeId.Create("boundary-heat-" + id), DeclarationHandle.Create(Prefix + name),
            H(title), StatementSource.WithoutFormula(), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(description))), DescribeRole.Definition);

    private static Formula Ratio(int numerator, int denominator) =>
        new Formula.Fraction(new Formula.Number(numerator), new Formula.Number(denominator));

    private static Formula Decay(int rate, int denominator, Formula t) =>
        new Formula.Fraction(Call("exp", new Formula.Binary(
            new Formula.Negate(new Formula.Number(rate)), FormulaBinaryOperator.Multiply, t)),
            new Formula.Number(denominator));

    private static Formula All(string variable, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(variable), domain, body);

    private static Formula Eqn(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Ne(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.NotEqual, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
}
