using System.Linq;
using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Transport;

internal sealed class MatrixUnitGeneratorDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations.",
        H("MatrixUnitGenerator"),
        Blocks(new[]
        {
            "matrix_unit_transport_generator",
            "generator_from_real_path"
        }.Select(name => (DocumentBlock)Describe.Lean(
            DescribeId.Create(name.Replace('_', '-')),
            DeclarationHandle.Create("D5/S3/Quantum/Transport/MatrixUnitGenerator." + name),
            H(name.Replace('_', ' ')),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/Quantum/kato1950adiabatic")),
            Blocks(Paragraph(Text("The computed averaged derivative generates every moving logical matrix unit. A real differentiable-path adapter derives the tangent hypotheses. Dyson convergence, global ODE existence, and physical implementability are not assumed or certified by these declarations."))),
            DescribeRole.Theorem)).Concat(new DocumentBlock[]
        {
            Paragraph(Text("Euclidean operator-norm application. Let d and n be arbitrary finite index types, and let F and D be families of complex n by n matrices indexed by d by d. Assume only the full matrix-unit laws F(i,j)F(k,l) = delta(j,k)F(i,l) and F(i,j)* = F(j,i), where star is conjugate transpose and delta is the Kronecker delta. D is arbitrary. All matrix norms in this application are the operator norm on EuclideanSpace over the complex numbers, selected in Lean by Matrix.Norms.L2Operator.")),
            Paragraph(Text("Write P = unitSupport(F), the sum of F(i,i) over d, and V(D) = supportVelocity(D), the sum of D(i,i) over d. Write K(F,D) = transportGenerator(F,D) = Z - P V(D), where Z = averagedVelocity(F,D) is the complex reciprocal of card(d) times the double sum of D(i,j)F(j,i). These are the existing computed operators. Real and complex reciprocals are totalized, with the reciprocal of zero equal to zero.")),
            Paragraph(Text("In the formula, FiniteTypes denotes finite index types, MatrixFamily(d,n) denotes d -> d -> Matrix n n C, MatrixUnits(F) denotes precisely the two laws above, ComplexI is the imaginary unit, and h is the positive real parameter hbar. For every such family and every such h, the following bound follows from the existing C-star and norm inequalities; the two owner theorems above do not themselves state this estimate.")),
            Paragraph(Math(Disp(Seq(
                Forall, Sp, F.Id("d"), Comma, Sp, F.Id("n"), Sp, InMacro, Sp,
                    Call("FiniteTypes"), Comma, Esc,
                Forall, Sp, F.Id("F"), Comma, Sp, F.Id("D"), Sp, InMacro, Sp,
                    Call("MatrixFamily", F.Id("d"), F.Id("n")), Comma, Esc,
                Forall, Sp, F.Id("h"), Sp, InMacro, Sp, Mathbb, Grp(F.Id("R")), Comma, Esc,
                Open, Call("MatrixUnits", F.Id("F")), Sp, Land, Sp,
                    D(0), Sp, Lt, Sp, F.Id("h"), Close, Sp, Implies, Sp,
                Norm(Seq(Call("ComplexI"), Sp, F.Id("h"), Sp,
                    Call("K", F.Id("F"), F.Id("D")))), Sp, Le, Sp,
                F.Id("h"), Open,
                    Frac, Grp(D(1)), Grp(Call("card", F.Id("d"))), Sp,
                    Sum, Underscore, Grp(Seq(F.Id("i"), Sp, InMacro, Sp, F.Id("d"))), Sp,
                    Sum, Underscore, Grp(Seq(F.Id("j"), Sp, InMacro, Sp, F.Id("d"))), Sp,
                    Norm(Call("D", F.Id("i"), F.Id("j"))), Sp, Plus, Sp,
                    Norm(Call("V", F.Id("D"))), Close)))),
            Paragraph(Text("The multiplication and star laws make P and each F(j,j) self-adjoint idempotents. IsStarProjection.norm_le therefore gives norm(P) <= 1 and norm(F(j,j)) <= 1, including zero projections. Matrix.l2_opNorm_conjTranspose_mul_self, the matrix form of CStarRing.norm_star_mul_self, gives norm(F(i,j)) squared = norm(F(j,j)); hence every matrix unit has norm at most one. No equality to one is needed.")),
            Paragraph(Text("By Matrix.l2_opNorm_mul, each norm(D(i,j)F(j,i)) is at most norm(D(i,j)). Two applications of norm_sum_le and norm_smul bound norm(Z) by the real reciprocal of card(d) times the double sum of norm(D(i,j)). The same product inequality gives norm(P V(D)) <= norm(V(D)). Finally norm_sub_le bounds norm(K) by their sum, and norm_smul with norm(ComplexI times h) = h gives the displayed inequality. This is a direct application of the existing library estimates to the computed generator.")),
            Paragraph(Text("For a differentiable matrix-unit path, substitute its value at a time t for F and its entrywise derivative at t for D. Differentiating the finite diagonal sum identifies supportVelocity(D) with the derivative of P. Thus D = dot F and supportVelocity(D) = dot P give exactly the geometric-term bound in ST40.1. The norm estimate itself uses neither differentiated multiplication nor differentiated star hypotheses; the owner generator theorems use those additional relations to prove skew-adjointness and the commutator equations.")),
            Paragraph(Text("The definitions and estimate require neither index type to be nonempty. An empty logical index makes both sums, P, V and K zero. An empty physical index also gives zero matrices. A zero family F gives K = 0 for arbitrary D, and proper support is allowed. Faithfulness, full rank, full support and nonzero matrix units are unnecessary. For arbitrary D this estimate asserts no skew-adjointness, Hamiltonian realization or transport existence. It supplies no device bandwidth, energy cost, locality or physical attainability conclusion, and does not establish the remaining Hamiltonian and evolution assertions of ST40.1."))
        }).ToArray())));

    private static Formula Norm(Formula value) => Seq(Vert, Sp, value, Vert);

}
