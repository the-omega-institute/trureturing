using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ArithUnits;

internal sealed class MercaPrimeCharacterMomentDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ArithUnits/MercaPrimeCharacterMoment.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/ArithUnits/yaoxu2026catalanmoment");
    private static readonly Formula n = F.Id("n"), p = F.Id("p"), a = F.Id("a"),
        u = F.Id("u");
    private static Formula Chi => F.Id("c");
    private static Formula Nat => Seq(Mathbb, Grp(F.Id("N")));
    private static Formula Complex => Seq(Mathbb, Grp(F.Id("C")));
    private static Formula Call(string name, Formula x) =>
        Seq(Operatorname, Grp(F.Id(name)), Open, x, Close);
    private static Formula Units(Formula x) => Seq(Open, Mathbb, Grp(F.Id("Z")), Slash,
        x, Mathbb, Grp(F.Id("Z")), Close, Caret, Grp(Times));
    private static Formula Char(Formula x) => Seq(Operatorname, Grp(F.Id("DirichletCharacter")),
        Open, Complex, Comma, x, Close);
    private static Formula All(Formula x, Formula type, Formula body) =>
        Seq(Forall, Sp, Open, x, Colon, type, Close, Comma, Sp, body);
    private static Formula Moment(Formula x) => Seq(F.Id("A"), Underscore, Grp(x), Open, Chi, Close);
    private static Formula Weight(Formula x) => Seq(Call("val", x), Sp, Chi, Open, x, Close);
    private static Formula UnitSum(Formula x) => Seq(Sum, Underscore,
        Grp(u, Colon, Units(x)), Sp, Weight(u));
    private static Formula ZmodSum(Formula x) => Seq(Sum, Underscore,
        Grp(a, Colon, Call("ZMod", x)), Sp, Weight(a));
    private static Formula Positive(Formula x, Formula body) =>
        All(x, Nat, Seq(OpenBracket, Call("NeZero", x), CloseBracket, Sp,
            All(Chi, Char(x), body)));

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The first character moment over actual residue units equals the all-residue weighted sum. "
            + "For a prime modulus, a nonprincipal odd character has a nonzero moment.",
        H("Prime Odd-Character Moments on Native Units"),
        Blocks(
            Paragraph(Text("All sums take values in the complex numbers. Each weight is the natural "
                + "representative of the residue, coerced before multiplication. The units are the "
                + "same native unit groups used for the least-residue coset moments. At a modulus "
                + "greater than one their representatives are positive and strictly below the modulus. "
                + "The definition and extension-by-zero equality require only NeZero n, and include n = 1: "
                + "the sole residue has natural representative zero, so both weighted sums vanish. "
                + "Character values at units mean values at their underlying ZMod residues. "
                + "The prime nonvanishing argument uses the licensed Yao Xu supplier cited below. "
                + "In the displayed formulas c denotes the source character χ.")),
            Paragraph(Text("Audit status (current evidence): exactly three Reg source-equivalence records are declared_validated: Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.argumentFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.arg_one_sub_exp_two_pi; Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.family for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.hurwitzZeta_apply_zero_of_mem_Ioo; and Reg.D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sineFamily for D5.S3.Analytic.Zeta.CatalanPrimeOddMoment.sinZeta_one_eq_of_mem_Ioo. The continuation is open/unknown, with 17 additional unvalidated unfinished audit targets tracked at https://github.com/the-omega-institute/trureturing/issues/17346#issuecomment-6304013114. These three records do not complete the 17 audits and do not establish an inexhaustibility result. The current evidence ceiling is standard axiom closure, not Reg admission completion or a full audit certificate. The archived extension_by_zero consumer failure remains un-restored. Exact remaining exclusions are the composite induced-character weighted-moment identity, strict sign, class-number formula, collision converse, quartic or sextic family conclusions, and broader 21-paper completion.")),
            Node("definition", "The unit character moment", "characterMoment",
                Positive(n, Seq(Moment(n), Sp, Eq, Sp, UnitSum(n))),
                "The sum ranges over every actual unit exactly once.", DescribeRole.Definition),
            Node("bridge", "Extension by zero on nonunits", "character_moment_eq_zmod_sum",
                Positive(n, Seq(Moment(n), Sp, Eq, Sp, ZmodSum(n))),
                "The unit coercion is injective. Every residue outside its image is a nonunit, "
                    + "where a Dirichlet character vanishes. Mapping the finite unit set and "
                    + "adjoining these zero summands proves the equality.", DescribeRole.Theorem),
            Node("nonvanishing", "Nonvanishing at the full prime odd-character domain",
                "prime_odd_character_moment_ne_zero",
                All(p, Nat, Seq(OpenBracket, Call("Prime", p), CloseBracket, Sp,
                    All(Chi, Char(p), Seq(Chi, Neq, D(1), Sp, Land, Sp,
                        Chi, Open, Minus, D(1), Close, Eq, Minus, D(1), Sp, Rightarrow, Sp,
                        Moment(p), Neq, D(0))))),
                "Apply the prime odd-character weighted-sum theorem to the preceding finite-sum "
                    + "identity. The nonprincipal and odd hypotheses remain explicit. This result "
                    + "supplies the prime moment required by the Merca collision converse. It does "
                    + "not assert the corresponding formula at a composite induced level, or the "
                    + "collision, quartic or sextic family conclusions.", DescribeRole.Theorem))));

    private static DocumentBlock Node(string id, string title, string declaration,
        Formula statement, string prose, DescribeRole role) => Describe.Lean(
            DescribeId.Create("merca-prime-character-" + id), DeclarationHandle.Create(Prefix + declaration),
            H(title), StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(Source),
            Blocks(Paragraph(Text(prose))), role);
}
