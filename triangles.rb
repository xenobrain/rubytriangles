module Triangles
  @edge_stack = Array.new(512)

  class << self
    def earclip(vertices)
      triangles_indices = []
      n = vertices.size >> 1
      indices = (0...n).to_a

      while n > 3
        i = 0
        found_ear = false

        while i < n
          i1 = indices[i]
          i2 = indices[(i + 1) % n]
          i3 = indices[(i + 2) % n]

          ax = vertices[i1 << 1]
          ay = vertices[(i1 << 1) + 1]
          bx = vertices[i2 << 1]
          by = vertices[(i2 << 1) + 1]
          cx = vertices[i3 << 1]
          cy = vertices[(i3 << 1) + 1]

          if ((bx - ax) * (cy - ay) - (by - ay) * (cx - ax)) > Float::EPSILON
            is_ear = true

            j = 0
            while j < n
              if j != i && j != (i + 1) % n && j != (i + 2) % n
                px, py = vertices[indices[j] << 1], vertices[(indices[j] << 1) + 1]
                if ((cx - ax) * (py - ay) - (cy - ay) * (px - ax)) >= 0 &&
                  ((ax - bx) * (py - by) - (ay - by) * (px - bx)) >= 0 &&
                  ((bx - cx) * (py - cy) - (by - cy) * (px - cx)) >= 0
                  is_ear = false
                  break
                end
              end
              j += 1
            end

            if is_ear
              triangles_indices << i1 << i2 << i3
              indices.delete_at((i + 1) % n)
              found_ear = true
              n -= 1
              break
            end
          end

          i += 1
        end

        raise "Could not triangulate vertices: #{vertices}" unless found_ear
      end

      triangles_indices.concat(indices) if n == 3
      triangles_indices
    end

    def delaunay(coords)
      n = coords.length >> 1

      # Arrays to store the triangulation graph
      max_triangles = [2 * n - 5, 0].max
      triangles = Array.new(max_triangles * 3, 0)
      half_edges = Array.new(max_triangles * 3, 0)

      link = proc do |a, b|
        half_edges[a] = b
        half_edges[b] = a if b != -1
      end

      # Temporary arrays for tracking the edges of teh advancing convex hull
      hash_size = Math.sqrt(n).ceil
      hull_prev = Array.new(n)
      hull_next = Array.new(n)
      hull_tri = Array.new(n, 0)
      hull_hash = Array.new(hash_size)

      # Temporary arrays for sorting points
      ids = Array.new(n)
      dists = Array.new(n)

      #region update

      # Populate and array of point indices, calculate the bounding box
      min_x = Float::INFINITY
      min_y = Float::INFINITY
      max_x = -Float::INFINITY
      max_y = -Float::INFINITY

      i = 0
      while i < n
        x = coords[2 * i]
        y = coords[2 * i + 1]

        min_x = x if x < min_x
        min_y = y if y < min_y
        max_x = x if x > max_x
        max_y = y if y > max_y
        ids[i] = i
        i += 1
      end

      cx = (min_x + max_x) * 0.5
      cy = (min_y + max_y) * 0.5

      hash_key = proc { |kx, ky| (psuedo_angle(kx - cx, ky - cy) * hash_size).floor % hash_size }

      i0 = i1 = i2 = 0
      min_dist = Float::INFINITY

      i = 0
      while i < n
        d = dist(cx, cy, coords[2 * i], coords[2 * i + 1])
        if d < min_dist
          i0 = i
          min_dist = d
        end

        i += 1
      end

      i0x = coords[2 * i0]
      i0y = coords[2 * i0 + 1]
      min_dist = Float::INFINITY

      i = 0
      while i < n
        if i == i0
          i += 1
          next
        end

        d = dist(i0x, i0y, coords[2 * i], coords[2 * i + 1])
        if d < min_dist && d > 0
          i1 = i
          min_dist = d
        end

        i += 1
      end

      i1x = coords[2 * i1]
      i1y = coords[2 * i1 + 1]
      min_radius = Float::INFINITY

      i = 0
      while i < n
        if i == i1 || i == i1
          i += 1
          next
        end
        r = circumradius(i0x, i0y, i1x, i1y, coords[2 * i], coords[2 * i + 1])
        if r < min_radius
          i2 = i
          min_radius = r
        end

        i += 1
      end

      i2x = coords[2 * i2]
      i2y = coords[2 * i2 + 1]

      if min_radius == Float::INFINITY
        i = 0
        while i < n
          dists[i] = (coords[2 * i] - coords[0]) || (coords[2 * i + 1] - coords[1])
          i += 1
        end

        quicksort(ids, dists, 0, n - 1)

        hull = Array.new(n)
        d0 = -Float::INFINITY
        j = 0
        i = 0
        while i < n
          id = ids[i]
          d = dists[id]
          if d > d0
            hull[j] = id
            d0 = d
            j += 1
          end
          i += 1
        end

        hull = hull.slice(0, j)
        triangles = Array.new(0)
        half_edges = Array.new(0)
        return { hull: hull, triangles: triangles, half_edges: half_edges }
      end

      if orient2d(i0x, i0y, i1x, i1y, i2x, i2y) < 0
        i = i1
        x = i1x
        y = i1y
        i1 = i2
        i1x = i2x
        i1y = i2y
        i2 = i
        i2x = x
        i2y = y
      end

      center = circumcenter(i0x, i0y, i1x, i1y, i2x, i2y)
      cx, cy = center

      i = 0
      while i < n
        dists[i] = dist(coords[2 * i], coords[2 * i + 1], cx, cy)

        i += 1
      end

      quicksort(ids, dists, 0, n - 1)

      hull_start = i0
      hull_size = 3

      hull_next[i0] = hull_prev[i2] = i1
      hull_next[i1] = hull_prev[i0] = i2
      hull_next[i2] = hull_prev[i1] = i0
      hull_tri[i0] = 0
      hull_tri[i1] = 1
      hull_tri[i2] = 2

      hull_hash.fill(-1)
      hull_hash[hash_key[i0x, i0y]] = i0
      hull_hash[hash_key[i1x, i1y]] = i1
      hull_hash[hash_key[i2x, i2y]] = i2

      triangles_len = 0

      add_triangle = proc do |ti0, ti1, ti2, a, b, c|
        t = triangles_len

        triangles[t] = ti0
        triangles[t + 1] = ti1
        triangles[t + 2] = ti2

        link[t, a]
        link[t + 1, b]
        link[t + 2, c]

        triangles_len += 3
        t
      end

      add_triangle[i0, i1, i2, -1, -1, -1]
      num_ids = ids.length
      xp = yp = 0
      k = 0

      while k < num_ids
        i = ids[k]
        x = coords[2 * i]
        y = coords[2 * i + 1]

        if k > 0 && (x - xp).abs <= Float::EPSILON && (y - yp).abs <= Float::EPSILON
          k += 1
          next
        end

        xp = x
        yp = y

        if i == i0 || i == i1 || i == i2
          k += 1
          next
        end

        start = 0
        j = 0
        key = hash_key[x, y]
        while j < hash_size
          start = hull_hash[(key + j) % hash_size]
          break if start != -1 && start != hull_next[start]
          j += 1
        end

        start = hull_prev[start]
        e = start

        while e
          q = hull_next[e]

          break if orient2d(x, y, coords[2 * e], coords[2 * e + 1], coords[2 * q], coords[2 * q + 1]) < 0

          e = q
          if e == start
            e = -1
            break
          end
        end

        next if e == -1

        legalize = proc do |a|
          i = ar = 0

          while true
            b = half_edges[a]

            a0 = a - a % 3
            ar = a0 + (a + 2) % 3

            if b == -1
              break if i == 0
              a = @edge_stack[i]
              i -= 1
              next
            end

            b0 = b - b % 3
            al = a0 + (a + 1) % 3
            bl = b0 + (b + 2) % 3

            p0 = triangles[ar]
            pr = triangles[a]
            pl = triangles[al]
            p1 = triangles[bl]

            illegal = in_circle(
              coords[2 * p0], coords[2 * p0 + 1],
              coords[2 * pr], coords[2 * pr + 1],
              coords[2 * pl], coords[2 * pl + 1],
              coords[2 * p1], coords[2 * p1 + 1]
            )

            if illegal
              triangles[a] = p1
              triangles[b] = p0

              hbl = half_edges[bl]

              if hbl == -1
                e = hull_start

                begin
                  if hull_tri[e] == bl
                    hull_tri[e] = a
                    break
                  end
                  e = hull_prev[e]
                end while e != hull_start
              end

              link[a, hbl]
              link[b, half_edges[ar]]
              link[ar, bl]

              br = b0 + (b + 1) % 3

               if i < @edge_stack.length
                 @edge_stack[i] = br
                 i += 1
              end
            else
              break if i == 0
              a = @edge_stack[i]
              i -= 1
            end
          end

          ar
        end

        # Add the first triangle from the point
        t = add_triangle[e, i, hull_next[e], -1, -1, hull_tri[e]]

        # Recursively flip triangles from the point until they satisfy the Delaunay condition
        hull_tri[i] = legalize[t + 2]
        hull_tri[e] = t # Keep track of boundary triangles on the hull
        hull_size += 1

        # Walk forward through the hull, adding more triangles and flipping recursively
        n = hull_next[e]
        q = hull_next[n]
        while orient2d(x, y, coords[2 * n], coords[2 * n + 1], coords[2 * q], coords[2 * q + 1]) < 0
          t = add_triangle[n, i, q, hull_tri[i], -1, hull_tri[n]]
          hull_tri[i] = legalize[t + 2]
          hull_next[n] = n # Mark edge as removed
          hull_size -= 1
          n = q
        end

        # Walk backward from the other side, adding more triangles and flipping
        if e == start
          q = hull_prev[e]
          while orient2d(x, y, coords[2 * q], coords[2 * q + 1], coords[2 * e], coords[2 * e + 1]) < 0
            t = add_triangle[q, i, e, -1, hull_tri[e], hull_tri[q]]
            legalize[t + 2]
            hull_tri[q] = t
            hull_next[e] = e # Mark edge as removed
            hull_size -= 1
            e = q
          end
        end

        # Update the hull indices
        hull_start = hull_prev[i] = e
        hull_next[e] = hull_prev[n] = i
        hull_next[i] = n

        # Save the two new edges in the hash table
        hull_hash[hash_key[x, y]] = i
        hull_hash[hash_key[coords[2 * e], coords[2 * e + 1]]] = e

        k += 1
      end

      hull = Array.new(hull_size)
      e = hull_start
      i = 0
      while i < hull_size
        hull[i] = e
        e = hull_next[e]
        i += 1
      end

      # Trim the arrays
      triangles = triangles.slice(0, triangles_len)
      half_edges = half_edges.slice(0, triangles_len)

      { hull: hull, triangles: triangles, half_edges: half_edges }
    end

    def psuedo_angle(dx, dy)
      p = dx / dx.abs + dy.abs
      (dy > 0 ? 3 - p : 1 + p) / 4
    end

    def dist(ax, ay, bx, by)
      dx = ax - bx
      dy = ay - by
      dx * dx + dy * dy
    end

    def in_circle(ax, ay, bx, by, cx, cy, px, py)
      dx = ax - px
      dy = ay - py
      ex = bx - px
      ey = by - py
      fx = cx - px
      fy = cy - py

      ap = dx * dx + dy * dy
      bp = ex * ex + ey * ey
      cp = fx * fx + fy * fy

      dx * (ey * cp - bp * fy) -
        dy * (ex * cp - bp * fx) +
        ap * (ex * fy - ey * fx) < 0
    end

    def circumradius(ax, ay, bx, by, cx, cy)
      dx = bx - ax
      dy = by - ay
      ex = cx - ax
      ey = cy - ay

      bl = dx * dx + dy * dy
      cl = ex * ex + ey * ey
      d = 0.5 / (dx * ey - dy * ex)

      x = (ey * bl - dy * cl) * d
      y = (dx * cl - ex * bl) * d

      x * x + y * y
    end

    def circumcenter(ax, ay, bx, by, cx, cy)
      dx = bx - ax
      dy = by - ay
      ex = cx - ax
      ey = cy - ay

      bl = dx * dx + dy * dy
      cl = ex * ex + ey * ey
      d = 0.5 / (dx * ey - dy * ex)

      x = ax + (ey * bl - dy * cl) * d
      y = ay + (dx * cl - ex * bl) * d

      [x, y]
    end

    def orient2d(ax, ay, bx, by, cx, cy)
      (ay - cy) * (bx - cx) - (ax - cx) * (by - cy)
    end

    def quicksort(ids, dists, left, right)
      if right - left <= 20
        i = left + 1
        while i <= right
          temp = ids[i]
          temp_dist = dists[temp]
          j = i - 1
          while j >= left && dists[ids[j]] > temp_dist
            ids[j + 1] = ids[j -= 1]
            ids[j + 1] = temp
          end
          i += 1
        end
      else
        median = (left + right) >> 1
        i = left + 1
        j = right
        swap(ids, median, i)
        swap(ids, left, right) if dists[ids[left]] > dists[ids[right]]
        swap(ids, i, right) if dists[ids[i]] > dists[ids[right]]
        swap(ids, left, i) if dists[ids[left]] > dists[ids[i]]

        temp = ids[i]
        temp_dist = dists[temp]
        while true
          begin i += 1 end while dists[ids[i]] < temp_dist
          begin j -= 1 end while dists[ids[j]] > temp_dist
          break if j < i
          swap(ids, i, j)
        end
        ids[left + 1] = ids[j]
        ids[j] = temp

        if right - i + 1 >= j - left
          quicksort(ids, dists, i, right)
          quicksort(ids, dists, left, j - 1)
        else
          quicksort(ids, dists, left, j - 1)
          quicksort(ids, dists, i, right)
        end
      end
    end

    def swap(arr, i, j)
      tmp = arr[i]
      arr[i] = arr[j]
      arr[j] = tmp
    end

    def default_get_x(p)
      p[0]
    end

    def default_get_y(p)
      p[1]
    end
  end
end
