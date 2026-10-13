using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.ModularForms;

internal sealed class IntegralMillerBasisDocument : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef ClassicalSource =
        LibraryNoteRef.Create("D5/L/Fourier/sage2026victormillerbasis");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A constructed integral Miller basis, its exact coefficient coordinates and the full integer coefficient lattice.",
        H("Integral Miller Basis and Coefficient Lattice"),
        Blocks(
            Paragraph(Text(
                "Let m be a positive natural number and let s be one of 0, 4, 6, 8, 10, 14. Put k=12m+s. Every form below belongs to Mathlib's actual complex level-one CuspForm space of weight k. For zero-based j in Fin m, start with G_j=Delta^(j+1) E4^(3(m-1-j)+a) E6^b, where s=4a+6b and the six exponent pairs are (0,0), (1,0), (0,1), (2,0), (1,1), (2,1). All weight casts are proved.")),
            Paragraph(Text(
                "Write g_j(n) for the integer coefficient of G_j. This is computed by integer divisor sums, the delivered discriminantCoefficient algorithm, finite convolution, and structural natural-power recursion. In descending depth d=m-1-j define B(d,n)=g_(m-1-d)(n)-sum_(ell in Fin d) g_(m-1-d)(m-ell) B(ell,n). Every recursive call has smaller depth. The actual cusp form is defined by the identical subtraction and integer-cast scalar recursion. Neither executable coefficient function evaluates an analytic coefficient or selects an inverse image.")),
            Describe.Lean(
                DescribeId.Create("miller-all-coefficient-bridge"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.millerForm_coefficient"),
                H("All coefficients of the constructed forms"),
                StatementSource.FromAuthor(Disp(Equal(
                    Call("a", Call("F", F.Id("j")), F.Id("n")),
                    Call("cast", Call("millerCoefficient", F.Id("m"), F.Id("s"), F.Id("j"), F.Id("n")))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural m, every allowed residual s, every j in Fin m and every n including zero, coefficient n of the actual millerForm is the complex image of millerCoefficient(m,s,j,n). The proof first identifies the integer raw series with the actual analytic products, then follows the same well-founded recursion on both sides. Integrality is derived for every coefficient, rather than supplied as a basis hypothesis.")),
                    Paragraph(Text(
                    "The raw leading-order proof factors qExpansion(Delta)=X*tail with constantCoeff(tail)=1. Each raw G_j has zero coefficients below j+1 and coefficient one at j+1. Descending elimination cancels every larger index up through m. This normalization supplies the linear independence of the actual family."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-first-coefficient-equivalence"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.millerCoefficientEquiv_apply"),
                H("The first m coefficients are the complex coordinates"),
                StatementSource.FromAuthor(Disp(Equal(
                    Call("coordinate", F.Id("f"), F.Id("j")),
                    Call("a", F.Id("f"), Add(F.Id("j"), D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For m>=1 the constructed normalized family is a basis, and millerCoefficientEquiv is a complex-linear equivalence from the actual cusp space to Fin m -> C. Its coordinate j is exactly coefficient j+1. Reconstruction is f=sum_j a(f,j+1) F_j.")),
                    Paragraph(Text(
                    "The dimension argument uses Mathlib's CuspForm.discriminantEquiv and dimension_level_one. Division by Delta reduces the weight to 12(m-1)+s. For s=14 the weight-two residue correction gives dimension m; using floor(k/12) for the cusp dimension would give the wrong result. No dimension or basis assumption is added to the input."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-normalized-form-uniqueness"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.millerForm_unique"),
                H("Uniqueness of each normalized form"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Forall, Sp, F.Id("i"), Sp, Colon, Sp,
                    Call("Fin", F.Id("m")), Comma, Sp,
                    Call("a", F.Id("f"), Add(F.Id("i"), D(1))), Sp, Eq, Sp,
                    Call("delta", F.Id("i"), F.Id("j")), Close, Sp, Rightarrow, Sp,
                    F.Id("f"), Sp, Eq, Sp, Call("F", F.Id("j"))))),
                AssessedProvenance.FromLiterature(ClassicalSource),
                Blocks(Paragraph(Text(
                    "If an actual cusp form has first-m coefficients equal to the j-th coordinate vector, it is the constructed F_j. The statement quantifies over every j in Fin m and every actual form. The proof applies the injective coefficient equivalence, so uniqueness refers to the full analytic form."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-all-integer-first-integer"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.miller_integrality_iff"),
                H("Integral coefficients are determined by the first m"),
                StatementSource.FromAuthor(Disp(Seq(
                    Call("allIntegral", F.Id("f")), Sp, Leftrightarrow, Sp,
                    Call("firstIntegral", F.Id("m"), F.Id("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "An actual cusp form has every natural coefficient in the integer embedding into C if and only if its coefficients 1 through m are in that embedding. The forward implication selects those indices. In the reverse implication, reconstruction expresses every coefficient as a finite integer linear combination of the constructed integral coefficient sequences. The coefficient at zero remains in the quantified conclusion."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-integer-bound-sharp"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.miller_integrality_bound_sharp"),
                H("The number of coefficients is optimal"),
                StatementSource.FromAuthor(Disp(Seq(
                    F.Id("r"), Sp, Lt, Sp, F.Id("m"), Sp, Rightarrow, Sp,
                    Exists, Sp, F.Id("f"), Comma, Sp,
                    Call("firstIntegral", F.Id("r"), F.Id("f")), Sp, Land, Sp,
                    Neg, Call("allIntegral", F.Id("f"))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "For every natural m, allowed s, and r<m, there is an actual form whose coefficients 1 through r are integers but whose full coefficient sequence is not integral. Take one half of F_r with zero-based r in Fin m. Its first r coefficients are zero and its coefficient r+1 is one half, which cannot be an integer. The r=0 case is included."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("miller-integer-lattice-coordinate"),
                DeclarationHandle.Create("D5/S3/Arith/ModularForms/IntegralMillerBasis.millerIntegerLatticeEquiv_symm_coefficient"),
                H("The complete integer coefficient lattice"),
                StatementSource.FromAuthor(Disp(Equal(
                    Call("cast", Call("integerCoordinate", F.Id("f"), F.Id("j"))),
                    Call("a", F.Id("f"), Add(F.Id("j"), D(1)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "integralCuspLattice(k) is the Z-submodule of actual cusp forms with every coefficient integral. millerIntegerLatticeEquiv is a Z-linear equivalence from Fin m -> Z onto this entire submodule. Its forward map is the integer linear combination of the constructed F_j; its inverse coordinate, embedded in C, equals the actual coefficient j+1. The codomain is the full coefficient lattice, rather than a separately defined span with integrality assumed.")),
                    Paragraph(Text(
                    "The analytic basis and lattice equivalences are noncomputable. Their inverses do not enter millerCoefficientDepth or millerCoefficient, which remain executable integer recursions. The equivalences require m>=1; empty cusp spaces are outside their delivered range. FiniteHeckeArray consumes this basis and lattice API to prove that bottom-up integer arrays at precision pm+1 compute the actual prime Hecke matrix and preserve the full lattice, with an integer characteristic polynomial mapping to that of the analytic operator.")),
                    Paragraph(Text(
                    "Mathlib's pinned normalized Eisenstein, discriminant and exact dimension suppliers are recorded in the source note. This is a repository construction of classical level-one infrastructure; no mathematical originality, unique result, new Maeda case or solution of an external open problem is claimed."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] args) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. args]);
}
