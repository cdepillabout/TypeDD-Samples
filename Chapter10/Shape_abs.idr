module Shape_abs

export
data Shape = Triangle Double Double
           | Rectangle Double Double
           | Circle Double

export
triangle : Double -> Double -> Shape
triangle = Triangle

export
rectangle : Double -> Double -> Shape
rectangle = Rectangle

export
circle : Double -> Shape
circle = Circle

private
rectangle_area : Double -> Double -> Double
rectangle_area width height = width * height

export
area : Shape -> Double
area (Triangle base height) = 0.5 * rectangle_area base height
area (Rectangle length height) = rectangle_area length height
area (Circle radius) = pi * radius * radius


public export
data ShapeView : (shape : Shape) -> Type where
  TriangleView : ShapeView (triangle base height)
  RectangleView : ShapeView (rectangle width height)
  CircleView : ShapeView (circle radius)

shapeView : (shape : Shape) -> ShapeView shape
shapeView (Triangle x y) = TriangleView
shapeView (Rectangle x y) = RectangleView
shapeView (Circle x) = CircleView

areaView : (shape : Shape) -> Double
areaView shape with (shapeView shape)
  areaView (triangle base height) | TriangleView = (base * height) / 2
  areaView (rectangle width height) | RectangleView = width * height
  areaView (circle radius) | CircleView = pi * radius * radius

