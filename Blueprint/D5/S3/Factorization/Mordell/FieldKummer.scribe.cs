using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Factorization.Mordell;

internal sealed class FieldKummerDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Common projective coverings and total Kummer fibers.",
        H("Common projective coverings and total Kummer fibers"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("field-kummer-context"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.Context"),
                H("Characteristic-zero field context"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Context packages an arbitrary carrier, field structure, characteristic-zero instance and decidable equality. Every characteristic-zero field supplies these data; classical decidable equality imposes no mathematical restriction. It contains no covering, image or desired-conclusion premise."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-twist"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.Twist"),
                H("Nonzero twist over a field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Twist packages a Context, a field element d and the hypothesis d is nonzero. Thus quantifying over Twist is exactly quantifying over every characteristic-zero field and every nonzero d. In particular every nonzero rational D gives d through its field embedding."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-representativechange"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.RepresentativeChange"),
                H("Square representative change data"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("RepresentativeChange packages a nonzero twist, old and new unit representatives b1,b2 and b1 prime,b2 prime, and units u,v satisfying b1 prime times u squared equals b1 and b2 prime times v squared equals b2. These equalities describe the representative change and assert no solubility or desired image. Equality of squareclasses supplies such unit square witnesses."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-commonrep"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.CommonRep"),
                H("Common tuple with three independent coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For field units b1,b2 and a third field coefficient b3, CommonRep is a nonzero tuple satisfying the two homogeneous equations with third coefficient b3. The locus is defined without reference to a desired Kummer image."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-commonrel"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.CommonRel"),
                H("Common scaling with independent coefficients"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The same field unit scales every coordinate of the independent-coefficient common locus."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-commoncovering"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.CommonCovering"),
                H("Independent third representative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The common projective locus allows any third field unit b3; its equations and quotient are independent of any membership certificate."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-changerepresentatives"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.changeRepresentatives"),
                H("Equivalence under square representative changes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("If b1 prime times u squared equals b1 and b2 prime times v squared equals b2, multiplying z1,z2,z3 by u,v,uv respectively defines an equivalence of the entire common projective coverings. Its inverse uses the inverse units. No affine normalization or nonvanishing coordinate assumption is required."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-project-changerepresentatives"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.project_changeRepresentatives"),
                H("Actual point preserved by representative change"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representative equivalence preserves the projected actual curve point. The proof includes both the abscissa and ordinate when t is nonzero and the point at infinity when t is zero."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("field-kummer-normalizethird"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.normalizeThird"),
                H("Third-coefficient normalization"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For b3=b1*b2*w squared, multiplying z3 by w gives an equivalence from the independent-third-coefficient projective covering to the product-normalized covering. The inverse multiplies z3 by the inverse of w. All zero-coordinate and infinity cases remain in the common locus."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-normalizethirdofclass"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.normalizeThirdOfClass"),
                H("Normalization from the product-one squareclass convention"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The condition [b3]=[b1]+[b2] in additive squareclasses supplies a nonzero unit w with b3=b1*b2*w squared. Choosing this witness gives the full projective normalization equivalence. No quotient injectivity or reflection of squares is used."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-projectthird"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.projectThird"),
                H("Projection for the independent third representative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("With b3=b1*b2*w squared, projectThird projects after normalization. Its finite abscissa is b1*z1 squared/t squared and its ordinate is b1*b2*w*z1*z2*z3/t cubed. At t=0 it is infinity. Changing the choice of square root changes the corresponding orientation; normalization itself includes every exceptional point."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-curve"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.curve"),
                H("Split cubic over a field"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a field K and d in K, the curve has coefficients a1=a3=a6=0, a2=-10d and a4=-75d squared, so its affine equation is y squared=x(x+5d)(x-15d)."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-curve-is-elliptic"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.curve_is_elliptic"),
                H("Ellipticity"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every characteristic-zero field K and nonzero d, this curve is elliptic, with discriminant 36000000 times d to the sixth power."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("field-kummer-root"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.root"),
                H("Ordered roots"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The ordered roots are 0,-5d,15d."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-descentrep"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.descentRep"),
                H("Total coordinate representative"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The representative at infinity is one. At a finite point it is x-e away from the selected root e, and the cubic derivative 3e squared-20de-75d squared at x=e. The three derivative values are -75d squared,100d squared,300d squared."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-descentrep-add-square"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.descentRep_add_square"),
                H("Addition on all points"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every characteristic-zero field K, nonzero d, ordered root index i, and actual points P,Q, the product of the total representatives at P,Q,P+Q is a square in K. Secants, tangents, inverses, infinity and vanishing shifted coordinates are included."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("field-kummer-squareclass"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.SquareClass"),
                H("Field squareclasses"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The carrier is field units modulo the range of the square-power group homomorphism. Its additive form represents multiplication of squareclasses as addition. Zero is excluded only from the unit representatives, not from affine or covering coordinates."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-descentunit"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.descentUnit"),
                H("Nonzero descent units"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero d each total descent representative is a unit, including the derivative replacement at every root."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-coordinate"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.coordinate"),
                H("Single-coordinate homomorphism"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For nonzero d and every ordered root index, the total representative defines an additive homomorphism from the actual point group to additive field squareclasses."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-kummer"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.kummer"),
                H("Ordered Kummer homomorphism"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The Kummer homomorphism is the ordered pair of coordinates zero and one, corresponding to x and x+5d away from their zeros. Infinity maps to the additive pair (0,0). At T0 its representatives are (-75d squared,5d); at Tminus5d they are (-5d,100d squared); at T15d they are (15d,20d). All actual points are in its domain."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-descentrep-product-square"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.descentRep_product_square"),
                H("The third class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The product of all three total representatives at every actual point is a field square. Thus the third class is the sum of the first two classes in additive notation."))), DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("field-kummer-unitclass"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.unitClass"),
                H("Unit class"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("A field unit gives an element of the additive squareclass group."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-coveringrep"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.CoveringRep"),
                H("Common homogeneous locus"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For units b1,b2, a covering representative is one nonzero tuple (t,z1,z2,z3) satisfying b2*z2 squared-b1*z1 squared=5d*t squared and b1*z1 squared-b1*b2*z3 squared=15d*t squared. No Kummer membership is built into the locus. On this same tuple, addition gives b2*z2 squared-b1*b2*z3 squared=20d*t squared."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-projectiverel"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.ProjectiveRel"),
                H("Common projective scaling"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Two covering representatives are equivalent exactly when all four coordinates are multiplied by the same field unit."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-covering"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.Covering"),
                H("Projective two-covering"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The covering is the quotient of the independently defined common homogeneous locus by common nonzero scaling."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-projectrep"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.projectRep"),
                H("Actual elliptic projection"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("When t is nonzero the projection has x=b1*z1 squared/t squared and y=b1*b2*z1*z2*z3/t cubed. When t is zero the projection is the point at infinity. The homogeneous equations prove actual curve membership."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-project"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.project"),
                H("Projection on projective classes"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("The actual projected point is independent of common nonzero scaling, including its ordinate, and hence descends to the projective quotient."))), DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("field-kummer-covering-fiber"),
                DeclarationHandle.Create("D5/S3/Factorization/Mordell/FieldKummer.covering_fiber"),
                H("Exact fiber criterion"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For every characteristic-zero field K, every nonzero d, units b1,b2 and every actual curve point P, there exists a projective covering point projecting to P if and only if the total Kummer image of P is ([b1],[b2]). The construction includes infinity, every two-torsion root, y=0, t=0, and all permitted vanishing coordinates. It constructs a common tuple and adjusts its sign to match the actual ordinate. Consequently covering nonemptiness is equivalent to membership in the complete Kummer image; it is not a Selmer, Cassels-pairing, rank, generator, denominator, integrality or all-WSS theorem."))), DescribeRole.Theorem))));
}
