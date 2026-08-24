using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Observer.ArithmeticTomography;

internal sealed class ResidueCoordinateDimensionDocument : IScribeDocumentDefinition
{
    private const string LeanPrefix =
        "D5/S3/Observer/ArithmeticTomography/ResidueCoordinateDimension.";

    public DocumentDefinition Create()
    {
        Formula coordinate = F.Id("Coordinate");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula residuesThirty = Call("ZMod", D(3, 0));
        Formula q = F.Id("q");
        Formula n = F.Id("n");
        Formula s = F.Id("s");
        Formula t = F.Id("t");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula q2 = F.Id("q2");
        Formula q3 = F.Id("q3");
        Formula q5 = F.Id("q5");
        Formula q2q3 = Seq(OpenBrace, q2, Comma, Sp, q3, CloseBrace);
        Formula q2q5 = Seq(OpenBrace, q2, Comma, Sp, q5, CloseBrace);
        Formula q3q5 = Seq(OpenBrace, q3, Comma, Sp, q5, CloseBrace);
        Formula coordinateSets = Call("Finset", coordinate);

        return DocumentDefinition.Create(ScribeNode.Create(
            "Three prime-power residue coordinates on ZMod 30 have minimum complete coordinate count three.",
            H("Residue Coordinate Dimension"),
            Blocks(
                Describe.Lean(
                    DescribeId.Create("modulus-at-two-is-two"),
                    DeclarationHandle.Create(LeanPrefix + "q2_modulus"),
                    H("The coordinate at two has modulus two"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("coordinateModulus", q2), Sp, Eq, Sp, D(2), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The coordinate indexed by the prime two records residues modulo "
                                + "two. The exponent of two in thirty is one, so its associated "
                                + "prime-power modulus is exactly two."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("modulus-at-three-is-three"),
                    DeclarationHandle.Create(LeanPrefix + "q3_modulus"),
                    H("The coordinate at three has modulus three"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("coordinateModulus", q3), Sp, Eq, Sp, D(3), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The coordinate indexed by the prime three records residues modulo "
                                + "three. Since thirty contains only one factor of three, the "
                                + "coordinate modulus is three."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("modulus-at-five-is-five"),
                    DeclarationHandle.Create(LeanPrefix + "q5_modulus"),
                    H("The coordinate at five has modulus five"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("coordinateModulus", q5), Sp, Eq, Sp, D(5), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The coordinate indexed by the prime five records residues modulo "
                                + "five. The factor five occurs once in thirty, so the attached "
                                + "prime-power modulus is five."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("crt-readings-preserve-natural-residues"),
                    DeclarationHandle.Create(LeanPrefix + "reading_natCast"),
                    H("CRT readings preserve natural-number residues"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, q, Colon, Sp, coordinate, Comma, Sp,
                        n, Colon, Sp, naturals, Comma, Esc,
                        Call("reading", q, Call("residue", n, D(3, 0))),
                        Sp, Eq, Sp,
                        Call("residue", n, Call("coordinateModulus", q)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Reading the residue class of a natural number at any coordinate "
                                + "returns the residue class of the same number at that "
                                + "coordinate's prime-power modulus. This is the natural-cast "
                                + "compatibility of the Chinese remainder equivalence."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("crt-readings-preserve-zero"),
                    DeclarationHandle.Create(LeanPrefix + "reading_zero"),
                    H("CRT readings preserve zero"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, q, Colon, Sp, coordinate, Comma, Sp,
                        Call("reading", q, D(0)), Sp, Eq, Sp, D(0), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Every coordinate sends the zero state modulo thirty to zero in its "
                                + "prime-power residue ring. This is the zero-preservation law for "
                                + "the Chinese remainder ring equivalence."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("two-three-readings-merge-fifteen-and-twenty-one"),
                    DeclarationHandle.Create(LeanPrefix + "q2_q3_collision"),
                    H("The two-three readings merge fifteen and twenty-one"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Merges", q2q3, D(1, 5), D(2, 1)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The states fifteen and twenty-one are distinct modulo thirty, but "
                                + "they have the same residues modulo two and modulo three. The "
                                + "coordinate pair consisting of q2 and q3 therefore cannot "
                                + "distinguish them."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("two-five-readings-merge-zero-and-ten"),
                    DeclarationHandle.Create(LeanPrefix + "q2_q5_collision"),
                    H("The two-five readings merge zero and ten"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Merges", q2q5, D(0), D(1, 0)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Zero and ten are different states modulo thirty while agreeing "
                                + "modulo both two and five. Consequently the q2 and q5 readings "
                                + "merge this explicit pair."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("three-five-readings-merge-zero-and-fifteen"),
                    DeclarationHandle.Create(LeanPrefix + "q3_q5_collision"),
                    H("The three-five readings merge zero and fifteen"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Merges", q3q5, D(0), D(1, 5)), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Zero and fifteen are distinct modulo thirty yet have equal residues "
                                + "modulo three and modulo five. Thus the q3 and q5 coordinate "
                                + "pair is also incomplete."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("merging-persists-under-coordinate-restriction"),
                    DeclarationHandle.Create(LeanPrefix + "merges_of_subset"),
                    H("Merging persists under coordinate restriction"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, s, Comma, Sp, t, Colon, Sp, coordinateSets, Comma, Sp,
                        Forall, Sp, x, Comma, Sp, y, Colon, Sp, residuesThirty, Comma, Esc,
                        Open, s, Sp, Subseteq, Sp, t, Sp, Land, Sp,
                        Call("Merges", t, x, y), Close, Sp, Rightarrow, Sp,
                        Call("Merges", s, x, y), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "If a larger coordinate set gives identical joint readings for two "
                                + "distinct states, any subset gives identical readings for the "
                                + "same pair. Restricting an equal coordinate tuple cannot recover "
                                + "information that the larger tuple already lost."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("every-coordinate-is-two-three-or-five"),
                    DeclarationHandle.Create(LeanPrefix + "coordinate_cases"),
                    H("Every coordinate is two, three, or five"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, q, Colon, Sp, coordinate, Comma, Sp,
                        q, Sp, Eq, Sp, q2, Sp, Lor, Sp,
                        q, Sp, Eq, Sp, q3, Sp, Lor, Sp,
                        q, Sp, Eq, Sp, q5, Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "A coordinate is a prime factor of thirty. The only such primes are "
                                + "two, three, and five, so the coordinate type has exactly these "
                                + "three possibilities."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("fewer-than-three-coordinates-are-incomplete"),
                    DeclarationHandle.Create(LeanPrefix + "fewer_than_three_incomplete"),
                    H("Fewer than three coordinates are incomplete"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Forall, Sp, s, Colon, Sp, coordinateSets, Comma, Sp,
                        Call("card", s), Sp, Lt, Sp, D(3), Sp, Rightarrow, Sp,
                        Neg, Sp, Call("Complete", s), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Any selection of fewer than three coordinates omits at least one of "
                                + "q2, q3, and q5. According to which coordinate is absent, the "
                                + "selection lies inside one of the three colliding pairs above; "
                                + "the subset principle then supplies two states it cannot separate."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("all-three-coordinates-are-complete"),
                    DeclarationHandle.Create(LeanPrefix + "all_coordinates_complete"),
                    H("All three coordinates are complete"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Call("Complete", F.Id("univ")), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The full coordinate family records all prime-power components of a "
                                + "state modulo thirty. Equality of every selected reading is "
                                + "therefore equality under the complete Chinese remainder "
                                + "equivalence, whose injectivity forces the original states to agree."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("a-finite-complete-coordinate-set-exists"),
                    DeclarationHandle.Create(LeanPrefix + "complete_coordinate_set_exists"),
                    H("A finite complete coordinate set exists"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Exists, Sp, n, Colon, Sp, naturals, Comma, Sp,
                        Exists, Sp, s, Colon, Sp, coordinateSets, Comma, Esc,
                        Call("card", s), Sp, Eq, Sp, n, Sp, Land, Sp,
                        Call("Complete", s), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "The explicit set containing q2, q3, and q5 has cardinality three. "
                                + "Because these are all coordinates, it is the full coordinate "
                                + "set and is complete by Chinese remainder injectivity."))),
                    DescribeRole.Lemma),
                Describe.Lean(
                    DescribeId.Create("residue-coordinate-dimension-is-three"),
                    DeclarationHandle.Create(LeanPrefix + "statistical_dimension_eq_three"),
                    H("The residue-coordinate dimension is three"),
                    StatementSource.FromAuthor(Disp(Seq(
                        Operatorname, Grp(F.Id("statisticalDimension")),
                        Sp, Eq, Sp, D(3), Dot))),
                    AssessedProvenance.FromRepo(),
                    Blocks(
                        Paragraph(Text(
                            "Statistical dimension is the least cardinality of a complete finite "
                                + "coordinate selection. The three-coordinate selection gives the "
                                + "upper bound, while every smaller selection is incomplete, so "
                                + "the least complete cardinality is exactly three.")),
                        Paragraph(Text(
                            "The three pairwise collision witnesses establish minimality, and the "
                                + "full Chinese remainder reading establishes attainability. The "
                                + "result is therefore an exact dimension statement rather than "
                                + "only a bound."))),
                    DescribeRole.Theorem))));
    }
}
