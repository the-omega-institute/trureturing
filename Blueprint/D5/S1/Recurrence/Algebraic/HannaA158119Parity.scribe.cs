using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S1.Recurrence.Algebraic;

internal sealed class HannaA158119ParityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S1/Recurrence/Algebraic/HannaA158119Parity.";

    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/RecurrenceAlgebraic/hanna2009a158119");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Parity of the original factorial-product OGF, its reversion quotient, and its unsigned even coefficients.",
        H("Hanna's A158119 parity conjecture"),
        Blocks(
            Paragraph(Text("Paul D. Hanna's OEIS A158119 conjecture states: "
                + "a(m) == 1 (mod 2) iff m is a power of 2 or m=0. "
                + "The original integer OGF and quotient are taken from A155585 and A157308. "
                + "The pinned source is oeis/oeisdata commit 5d3c6f683f5e0f2876df39773b7e49710c4f5f80, "
                + "seq/A158/A158119.seq, seq/A157/A157308.seq and seq/A155/A155585.seq. "
                + "The source definition and bounded prior-work limits are documented in hanna2009a158119.")),
            Paragraph(Text("Related prior work: Vladimir Reshetnikov's ProveIt article at "
                + "commit b61f8e7e32b64b32a925c2d3cffab80bc20fb4c6, "
                + "SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/"
                + "oeis-sequence-asymptotics/a290569-power-weighted-dyck-moments/article.tex, "
                + "proves powers-of-two parity for the quartic sequence A338634. "
                + "The inspected text does not explicitly state the original A158119 result. "
                + "No priority or new-method claim is made here.")),
            Node("summand", "The original factorial-product summand",
                "For natural n, summand n is n! times X^n times the product, for k=1,...,n, "
                + "of the formal unit inverse of 1+2kX. The product at n=0 is 1. "
                + "Every denominator has constant coefficient 1.", DescribeRole.Definition),
            Node("F", "The original ordinary generating function",
                "The coefficient at degree d is the sum of the original summand coefficients "
                + "for n=0,...,d. All omitted terms are divisible by X^(d+1). "
                + "This is the coefficientwise meaning of the infinite ordinary generating "
                + "series in A155585; factorials multiply the coefficients.", DescribeRole.Definition),
            Node("Q", "The compositional inverse",
                "Q is the unique zero-constant compositional inverse of X*F over the integers. "
                + "The coefficient of X in X*F is 1, so Mathlib's unit-linear reversion applies.",
                DescribeRole.Definition),
            Node("B", "The normalized quotient",
                "B is F substituted at Q. Substitution into (X*F)(Q)=X gives B*Q=X. "
                + "Its constant coefficient is 1. Since Q is nonzero and the integer power "
                + "series ring is a domain, this uniquely specifies the original quotient X/Q.",
                DescribeRole.Definition),
            Node("a", "The original unsigned bisection",
                "a(m) is the natural absolute value of the integer coefficient of degree 2m "
                + "in B, for every natural m including zero.", DescribeRole.Definition),
            Node("quotient_equation", "The quotient identity",
                "The original compositional inverse equation gives this identity directly. "
                + "It is used in the parity proof to determine Q after reduction modulo two.",
                DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"),
                H("The full parity statement"), StatementSource.FromAuthor(ClaimFormula()),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "Modulo two the factors 2k vanish and n! vanishes for n at least two. "
                    + "Thus F reduces to 1+X, B reduces to 1+Q, and Q+Q^2=X. "
                    + "Mathlib's uniqueness of reversion identifies Q with the existing reduced "
                    + "Catalan series. CatalanCompositionSquareParity.binary_catalan supplies "
                    + "its powers-of-two support. Integer absolute value preserves oddness, "
                    + "and restricting the degree to 2m gives precisely the displayed equivalence. "
                    + "The zero index is included explicitly. This is an application of existing "
                    + "reversion and Catalan parity results; no new proof method is claimed."))),
                DescribeRole.Theorem, new OpenProblemResolutionClaim(
                    ProblemSlugRef.Create("hanna-a158119-original-parity"),
                    ResolutionKind.Proved)))));

    private static DocumentBlock Node(string name, string title, string prose, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace("_", "-").ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(prose))), role);

    private static Formula V(string s) => F.Id(s);
    private static Formula Nat() => Seq(Mathbb, Grp(V("N")));
    private static Formula Eqn(Formula x, Formula y) => Seq(x, Sp, Eq, Sp, y);
    private static Formula ClaimFormula() => Seq(Forall, Sp, V("m"), Colon, Sp, Nat(), Comma, Sp,
        new Formula.Apply(Seq(Operatorname, Grp(V("Odd"))),
            [new Formula.Apply(V("a"), [V("m")])]),
        Sp, Iff, Sp, Open, Eqn(V("m"), D(0)), Sp, Lor, Sp,
        Open, Exists, Sp, V("j"), Colon, Sp, Nat(), Comma, Sp,
        Eqn(V("m"), new Formula.Power(D(2), V("j"))), Close, Close);
}
