import { translate } from "sparqlalgebrajs";


const query = translate(`
PREFIX ex: <http://example.org/>

SELECT ?person ?info
WHERE {
  ?person a ex:Person .
  
  {
    # Outer UNION branch 1
    {
      # Inner UNION branch for location info
      { ?person ex:livesIn ex:CityA . BIND("Lives in CityA" AS ?info) }
      UNION
      { ?person ex:livesIn ex:CityB . BIND("Lives in CityB" AS ?info) }
    }
  }
  UNION
  {
    # Outer UNION branch 2
    {
      # Inner UNION branch for job info
      { ?person ex:hasOccupation ex:Engineer . BIND("Engineer" AS ?info) }
      UNION
      { ?person ex:hasOccupation ex:Artist . BIND("Artist" AS ?info) }
    }
  }
}`)

console.log(JSON.stringify(query, null, 2));