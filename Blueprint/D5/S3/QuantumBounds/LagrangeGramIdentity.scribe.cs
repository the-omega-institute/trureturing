using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuantumBounds;

internal sealed class LagrangeGramIdentityDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("The Cauchy-Schwarz defect equals a manifestly nonnegative sum of squares (the coordinate Gram remainder).",
        H("Lagrange-Gram Identity"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("lagrange-gram-identity"),
                DeclarationHandle.Create("D5/S3/QuantumBounds/LagrangeGramIdentity.lagrange_gram_identity"),
                H("The Cauchy-Schwarz defect is a sum of squares"),
                StatementSource.FromAuthor(Disp(Seq(
                    Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("u"), Underscore, Grp(F.Id("i")), Caret, Grp(D(2)), Close,
                    Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("v"), Underscore, Grp(F.Id("i")), Caret, Grp(D(2)), Close,
                    Minus, Open, Sum, Underscore, Grp(F.Id("i")), Sp, F.Id("u"), Underscore, Grp(F.Id("i")), F.Id("v"), Underscore, Grp(F.Id("i")), Close, Caret, Grp(D(2)),
                    Eq, Frac, Grp(D(1)), Grp(D(2)), Sp,
                    Sum, Underscore, Grp(F.Id("i")), Sp, Sum, Underscore, Grp(F.Id("j")), Sp,
                    Open, F.Id("u"), Underscore, Grp(F.Id("i")), F.Id("v"), Underscore, Grp(F.Id("j")), Minus, F.Id("u"), Underscore, Grp(F.Id("j")), F.Id("v"), Underscore, Grp(F.Id("i")), Close, Caret, Grp(D(2))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "For real families u and v indexed by a finite set, the Cauchy-Schwarz defect "
                        + "(sum of u_i^2)(sum of v_i^2) - (sum of u_i v_i)^2 equals one half of the double sum "
                        + "over i and j of (u_i v_j - u_j v_i)^2. The right-hand side is a sum of squares, hence "
                        + "nonnegative, which is exactly the Cauchy-Schwarz inequality; it is the coordinate form "
                        + "of the Gram wedge-remainder G in the identity ||u||^2 ||v||^2 = |<u,v>|^2 + G.")),
                    Paragraph(Text(
                        "The theorem establishes only this algebraic sum-of-squares identity; it does not "
                        + "instantiate the Cramer-Rao, Robertson-Schrodinger, or quantum Cramer-Rao specialisations "
                        + "of the note, which require the corresponding inner-product structures.")),
                    Paragraph(Text(
                        "For the six-coordinate scalar application, use the slot order (12,13,14,34,24,23) = (r,a,b,o,c,d), "
                        + "with every coordinate strictly greater than one. The target slot is 12 and its opposite slot is 34. "
                        + "Set R = r^2 - 1, A = R + a^2 + d^2 + 2rad, B = R + b^2 + c^2 + 2rbc, and W = ab + cd. "
                        + "Also set S = sqrt(ac) + sqrt(bd), C = R + (a-d)(c-b) + 2(r+1)sqrt(abcd), "
                        + "and J = (sqrt(AB) - C)/(r+1). These quantities are functions of the same six coordinates; J is not an independent parameter.")),
                    Paragraph(Text(
                        "Take U = (sqrt(R), a-d, sqrt(2(r+1)ad)) and V = (sqrt(R), c-b, sqrt(2(r+1)bc)) in Euclidean three-space. "
                        + "The positive square-root branches give ||U||^2 = A and ||V||^2 = B. "
                        + "Their dot product is U dot V = R + (a-d)(c-b) + 2(r+1)sqrt(ad)sqrt(bc) = C, "
                        + "because ad and bc are positive and sqrt(ad)sqrt(bc) = sqrt(abcd). "
                        + "In particular R, A, B, r+1, and sqrt(AB) are strictly positive.")),
                    Paragraph(Text(
                        "For these vectors the finite Gram identity gives AB - C^2 = N, where "
                        + "N = R((a-d)-(c-b))^2 + 2R(r+1)(sqrt(ad)-sqrt(bc))^2 "
                        + "+ 2(r+1)((a-d)sqrt(bc)-(c-b)sqrt(ad))^2. "
                        + "The three summands are the squared coordinate minors of U and V. "
                        + "All coefficients are positive, so N is nonnegative. Cauchy-Schwarz yields -sqrt(AB) ≤ C ≤ sqrt(AB), hence J ≥ 0.")),
                    Paragraph(Text(
                        "The denominator sqrt(AB) + C is strictly positive. If it were zero, Cauchy-Schwarz equality "
                        + "would make U and V point in opposite directions. Their first coordinates are the same positive number sqrt(R), "
                        + "which rules this out. Rationalizing sqrt(AB) - C therefore gives the exact expression "
                        + "J = N/((r+1)(sqrt(AB)+C)). This expression retains all three squared minors, "
                        + "including the contribution from the imbalance of the other two opposite pairs.")),
                    Paragraph(Text(
                        "The zero condition is J = 0 if and only if a = c and b = d. Indeed, J = 0 gives "
                        + "C = sqrt(AB), so Cauchy-Schwarz equality makes U and V point in the same direction. "
                        + "Their common positive first coordinate forces U = V. Thus a-d = c-b and ad = bc. "
                        + "Writing eta = a-c = d-b gives ad-bc = eta(a+b); since a+b > 0, eta = 0. "
                        + "Conversely, a = c and b = d makes U = V and J = 0.")),
                    Paragraph(Text(
                        "Define the original raw cosine expression by rawPhi = (W + r(ac+bd) - Ro)/sqrt(AB). "
                        + "Its positive denominator makes rawPhi ≤ -1 equivalent to Ro ≥ W + r(ac+bd) + sqrt(AB). "
                        + "Expanding S^2 = ac + bd + 2sqrt(abcd) and using (r+1)J = sqrt(AB)-C gives "
                        + "W + r(ac+bd) + sqrt(AB) = (r+1)(r-1+S^2) + (r+1)J. "
                        + "Since R = (r-1)(r+1) and r+1 > 0, this proves the scalar equivalence "
                        + "rawPhi ≤ -1 if and only if (r-1)(o-1) ≥ S^2 + J.")),
                    Paragraph(Text(
                        "When a = c and b = d, the positive square-root branches give S = a+b and the zero condition gives J = 0. "
                        + "The exact threshold then becomes rawPhi ≤ -1 if and only if (r-1)(o-1) ≥ (a+b)^2. "
                        + "For unequal opposite pairs, the term J must be retained in the equivalence.")),
                    Paragraph(Text(
                        "This calculation establishes a relation among the original scalar coordinates and raw cosine expression. "
                        + "To interpret rawPhi ≤ -1 as the flat sector with angles pi at slots 12 and 34, one additionally needs "
                        + "the native hyperideal length-domain identification on the entire positive length domain, including the sector boundary. "
                        + "The three-sector characterization and transport to the other opposite pairs must use actual tetrahedral vertex permutations. "
                        + "Those geometric inputs, including Luo-Yang Proposition 4.4, Proposition 4.5, and Lemma 4.6, are not established by the finite Gram identity "
                        + "or by this coordinate substitution; geometric realization and the global conclusions require their own hypotheses."))),
                DescribeRole.Theorem))));
}
